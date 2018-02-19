#![feature(stmt_expr_attributes)]
#![feature(swap_nonoverlapping)]

extern crate gcd;

use std::cmp::min;
use std::cmp::Ordering;

use gcd::Gcd;

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

pub const MAX_RECURSION_LIMIT: u32 = <u32>::max_value();

// Tuning parameters:

// The algorithm may use this many bytes on the stack as a buffer.  Only one buffer of this size
// exists on the stack at any time.
const STACK_OBJECT_SIZE: usize = 2048;

// The levels of recursion to allow. The recursive algorithm is O(log2(n)) in memory usage.
// Setting a limit to the recursion makes it O(1). Lower values use less stack, but are likely to
// be slower.  Values from 0 .. MAX_RECURSION_LIMIT are valid.
const RECURSION_LIMIT: u32 = MAX_RECURSION_LIMIT;

// The maximum GCD for which reverse is used to rotate. Above this value, block swapping is used.
const ROTATE_REVERSE_MAX: usize = 4;


fn gallop_right<T, F>(value: &T, buffer: &[T], compare: &F) -> usize
where
    F: Fn(&T, &T) -> Ordering
{
    // Find the insertion point in an ordered buffer where the value should be inserted to maintain
    // the ordering.  All elements to the left of the insertion point are Less than the value and
    // the value is Less than all elements to the right of the insertion point.  The ordering is
    // defined by the "compare" function.  The value is always on the left side of the comparison,
    // so, for stable sort, return Less if the value should stay left of any equal values, or
    // Greater if the value should stay right of any equal values. If the "compare" function
    // returns Equal, the function returns immediately with one (of possibly many) valid insertion
    // points. This is useful for unstable sort.
    let length = buffer.len();
    let mut lo = 0;       // lowest candidate
    let mut hi = length;  // highest candidate

    // First, gallop from the start of the sequence.  Galloping provides a middle ground between
    // pure binary search, which uses log2 n comparisons to find any position, and linear search,
    // which uses fewer comparisons for the earlier elements, but more for large runs.  Two of the
    // most common searches are:
    // - purely random, in which case there are probably only 1 or 2 elements at the start of a
    // subsequence that are less than the minimum element from the other sequence.
    // - mostly ordered, in which case comparing the left element against the zeroth element of the
    // righthand sequence should be fast.
    //
    // The gallop starts off slow at the start of the sequence, but increases exponentially to find
    // a range containing the position.  The searched positions are: 1, 3, 7, 15, 31,...
    let mut p2 = 2;
    while p2 - 1 < length {
        let trial = p2 - 1;
        match compare(value, &buffer[trial]) {
            Ordering::Less => {
                hi = trial;
                break;
            },
            Ordering::Greater => {
                lo = trial + 1;
                p2 *= 2;
            },
            Ordering::Equal => {
                #![cold]
                return trial;
            }
        }
    }

    // At this point, either hi == length, and we're processing the rump of the sequence, or
    // lo-hi contains 2^n - 1 elements containing the correct position.  2^n - 1 elements gives us
    // a balanced binary tree.  Perform binary search to find the final insertion position.
    debug_assert!(hi == length || (hi - lo + 1).is_power_of_two());
    binary_search(value, &buffer[lo .. hi], compare) + lo
}

fn binary_search<T, F>(value: &T, buffer: &[T], compare: &F) -> usize
where
    F: Fn(&T, &T) -> Ordering
{
    let length = buffer.len();
    let mut lo = 0;       // lowest candidate
    let mut hi = length;  // highest candidate
    while hi > lo {
        let trial = lo + (hi - lo) / 2;
        debug_assert!(trial < length);
        match compare(value, &buffer[trial]) {
            Ordering::Less => {
                hi = trial;
            },
            Ordering::Greater => {
                lo = trial + 1;
            },
            Ordering::Equal => {
                #![cold]
                return trial;
            },
        }
    }
    debug_assert!(lo == hi);
    lo
}

fn swap_ends<T>(s: &mut [T], k: usize) {
    // Swap front k items of sequence with back k items
    debug_assert!(k <= s.len() / 2);
    let b = s.len() - k;
    if k * std::mem::size_of::<T>() < 128 {
        for i in 0..k {
            unsafe {
                let pa: *mut T = s.get_unchecked_mut(i);
                let pb: *mut T = s.get_unchecked_mut(b + i);
                std::ptr::swap(pa, pb);
            }
        }
    } else {
        unsafe {
            let pa: *mut T = s.get_unchecked_mut(0);
            let pb: *mut T = s.get_unchecked_mut(b);
            std::ptr::swap_nonoverlapping(pa, pb, k);
        }
    }
}

fn add_modulo<T>(a: T, b: T, n: T) -> T
    where
        T: std::ops::Add<Output=T> + std::ops::Sub<Output=T> + Copy + PartialOrd
{
    // Return (a + b) % n
    // Faster than using the % operator, does not overflow
    debug_assert!(a >= n - n && a < n);
    debug_assert!(b >= n - n && b < n);
    let c = n - a;
    if b >= c {
        // b >= n - a  ->  b + a >= n.
        // a < n, b < n  ->  a + b < 2n
        // Hence: n <= a + b <= 2n - 1  ->  0 < a + b - n < n - 1
        // a + b - n  =  b - n + a  =  b - (n - a)  =  b - c
        b - c
    }
    else {
        // if b < n - a, then b + a < n, and in the modulo range
        a + b
    }
}

fn rotate_gcd<T>(s: &mut [T], k: usize) {
    // Rotate the last k elements to the front of the slice.
    // given a slice of 0..n, move n-k..n to front and 0..n-k to end
    let slen = s.len();
    debug_assert!(k > 0 && k < slen);
    // for i = 0..k, add size of second section: new position = (i + k) % slen
    // for i = k..slen, subtract size of first section: new position = (i - slen + k) % slen = (i + k) % slen
    // so all elements need to have the same move applied
    // There are gcd(k, slen-k) cycles
    let blksize = k.gcd(slen - k);
    if blksize < ROTATE_REVERSE_MAX {
        // If GCD is low, then we tend to stride through the slice moving a few elements at a
        // time.  In this case, the classic reverse everything twice algorithm performs faster.
        s.reverse();
        s[.. k].reverse();
        s[k ..].reverse();
    } else {
        // Otherwise, we move each block up by k positions, using the first block as working space.
        let mut j = k;
        for _ in 0 .. slen / blksize - 1 {
            swap_ends(&mut s[0 .. j + blksize], blksize);
            j = add_modulo(j, k, slen);
        }
        debug_assert!(j == 0);
    }
}

fn rotate_left_shift<T>(s: &mut [T], llen: usize) {
    debug_assert!(llen * std::mem::size_of::<T>() <= STACK_OBJECT_SIZE);
    let rlen = s.len() - llen;
    unsafe {
        // size_of is not const: https://github.com/rust-lang/rfcs/issues/1144
        // let mut tmp: [T; STACK_OBJECT_SIZE / std::mem::size_of::<T>()] = std::mem::uninitialized();
        // There's no way to express alignment: https://github.com/rust-lang/rfcs/issues/325
        // let mut tmp: [u8; STACK_OBJECT_SIZE] = std::mem::uninitialized();
        // However, using u8's also solves a potential problem.  If tmp is [T] and T is Drop, then
        // we need to use mem::forget to ensure the duplicated T's are not dropped.  This is easy,
        // as long as the code cannot panic.  In a panic, the forget is not run, but and drop still
        // runs.  There's a NoDrop trick using unstable unions, but using a type (like u8) that
        // is not Drop and then casting a pointer also prevents T::drop being called.
        // So, using u64 to improve alignment, this seems to be the best we can do right now:
        let mut tmp: [u64; STACK_OBJECT_SIZE / 8] = std::mem::uninitialized();
        let t = tmp.as_mut_ptr() as *mut T;
        let src = s.as_ptr();
        let dst = s.as_mut_ptr();
        std::ptr::copy_nonoverlapping(src, t, llen);
        std::ptr::copy(src.offset(llen as isize), dst, rlen);
        std::ptr::copy_nonoverlapping(t, dst.offset(rlen as isize), llen);
        // forget not needed but keeping it here to remind us in case tmp creation changes:
        // std::mem::forget(tmp);
    }
}

fn rotate_right_shift<T>(s: &mut [T], rlen: usize) {
    debug_assert!(rlen * std::mem::size_of::<T>() <= STACK_OBJECT_SIZE);
    let llen = s.len() - rlen;
    unsafe {
        let mut tmp: [u64; STACK_OBJECT_SIZE / 8] = std::mem::uninitialized();
        let t = tmp.as_mut_ptr() as *mut T;
        let src = s.as_ptr();
        let dst = s.as_mut_ptr();
        std::ptr::copy_nonoverlapping(src.offset(llen as isize), t, rlen);
        std::ptr::copy(src, dst.offset(rlen as isize), llen);
        std::ptr::copy_nonoverlapping(t, dst, rlen);
        // std::mem::forget(tmp);
    }
}

fn rotate<T>(s: &mut [T], rlen: usize) {
    // Rotate the last rlen elements to the front of the slice.
    // given a slice of 0..n, move n-rlen..n to front and 0..n-rlen to end
    let max_rotate_shift: usize = STACK_OBJECT_SIZE / std::mem::size_of::<T>();
    let length = s.len();
    debug_assert!(rlen <= length);
    let llen = length - rlen;
    if llen == 0 || rlen == 0 {
        return
    }
    match llen.cmp(&rlen) {
        Ordering::Less => {
            if llen <= max_rotate_shift {
                rotate_left_shift(s, llen);
                return
            }
        },
        Ordering::Greater => {
            if rlen <= max_rotate_shift {
                rotate_right_shift(s, rlen);
                return
            }
        },
        Ordering::Equal => {
            swap_ends(s, llen);
            return
        }
    }
    rotate_gcd(s, rlen);
}


fn trim<T, F, G>(s: &[T], split: usize, cmpleftright: &F, cmprightleft: &G) -> Option<(usize, usize)>
where
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    // Trim the low elements in L and high elements in R that are in their final position.
    //
    // Trimming is done in a specific order.  First l[max] is compared against r[0].  This ensures
    // that sequences that are in order use one comparison.   Much real data is close to already
    // sorted, so optimising this case is valuable.
    //
    // Then, a binary search of the l[max] value over R is done, as any values in R that are higher
    // than l[max] are already in their final position, and can be ignored.  In a typical mergesort,
    // the two sequences will each have length 2^n, and the first step means we search one less, or
    // `2^n - 1`.  This is the optimal size for binary search, as it means the search must take
    // `log2 n` comparisons.
    //
    // Finally, we check for values in L that are less than r[0], as they are also in their final
    // position.  In this case, we gallop right, since we expect r[0] to be lower than the median
    // value in L.
    let slen = s.len();
    let llen = split;
    let rlen = slen - split;

    if llen == 0 || rlen == 0 {
        return None;
    }

    // Check if sequences are already in order
    if cmpleftright(&s[split - 1], &s[split]) != Ordering::Greater {
        // l[max] <= r[0] -> L-R is already sorted
        return None;
    }
    // Trim off in-position high values of R to leave l[max] as largest value
    // From above, r[0] <= l[max], so exclude r[0] from search.
    let right = binary_search(&s[split - 1], &s[split + 1 .. slen], cmpleftright) + split + 1;

    // Trim off in-position low values of L to leave r[0] as smallest value
    // From above, l[max] >= r[0], so exclude l[max] from search.
    let left = gallop_right(&s[split], &s[.. split - 1], cmprightleft);

    Some((left, right))
}

fn merge<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G, recurse: u32)
where
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    if let Some((left, right)) = trim(s, split, cmpleftright, cmprightleft) {
        merge_trimmed(&mut s[left .. right], split - left, cmpleftright, cmprightleft, recurse);
    }
}

fn merge_trimmed<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G, recurse: u32)
where
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    if recurse == 0 {
        merge_final(s, split, cmpleftright, cmprightleft);
    } else {
        merge_recurse(s, split, cmpleftright, cmprightleft, recurse - 1);
    }
}

fn merge_recurse<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G, recurse: u32)
where
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    let mut left = 0;
    let mut split = split;
    let right = s.len();

    macro_rules! llen {() => (split - left)}
    macro_rules! rlen {() => (right - split)}

    // 1. |L| > 0
    debug_assert!(llen!() > 0);
    // 2. |R| > 0
    debug_assert!(rlen!() > 0);
    // 3. l_max is max value
    debug_assert!(cmprightleft(&s[right - 1], &s[split - 1]) == Ordering::Less);
    // 4. r_0 is min value
    debug_assert!(cmpleftright(&s[left], &s[split]) == Ordering::Greater);

    let mut highwater = 1; // elements of R known to be < l_0

    while llen!() > 1 && rlen!() > highwater {
        let xlen = gallop_right(&s[left], &s[split + highwater .. right], cmpleftright) + highwater;
        if xlen == rlen!() {
            break
        }
        // find Z in L where Z[i] < R'[0]
        // - Since L[max] > R[max], exclude L[max] from search
        // - Since R[split + xlen] > L[0] from previous search, exclude L[0] from search
        // - this search relies on invariant |L| > 1, tested in loop condition
        let zlen = gallop_right(&s[split + xlen], &s[left + 1 .. split - 1], cmprightleft) + 1;

        if llen!() <= xlen + zlen {
            rotate(&mut s[left .. split + xlen], xlen);
            left += xlen + zlen;
            split += xlen;
            highwater = 1;
        } else if zlen < xlen {
            swap_ends(&mut s[left .. split + xlen], xlen);
            left += xlen;
            let ml = split + zlen;
            let ms = xlen - zlen;
            let mr = gallop_right(
                &s[split + xlen - 1],
                &s[split + xlen + 1 .. right],
                cmpleftright
            ) + split + xlen + 1;
            merge_trimmed(&mut s[ml .. mr], ms, cmpleftright, cmprightleft, recurse);
            highwater = mr - split;
        } else {
            swap_ends(&mut s[left + zlen - xlen .. split + xlen], xlen);
            rotate(&mut s[left .. left + zlen], xlen);
            left += zlen;
            highwater = xlen + 1;
        }
    }
    // since r_0..r_highwater are < l_0, we just need to swap L and R
    // since l_max is largest value, if |L| = 1, we just need to swap L and R
    rotate(&mut s[left .. right], rlen!());
}

fn merge_final<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G)
where
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    let mut left = 0;
    let mut split = split;
    let right = s.len();

    macro_rules! llen {() => (split - left)}
    macro_rules! rlen {() => (right - split)}

    // 1. |L| > 0
    debug_assert!(llen!() > 0);
    // 2. |R| > 0
    debug_assert!(rlen!() > 0);
    // 3. l_max is max value
    debug_assert!(cmprightleft(&s[right - 1], &s[split - 1]) == Ordering::Less);
    // 4. r_0 is min value
    debug_assert!(cmpleftright(&s[left], &s[split]) == Ordering::Greater);

    let mut highwater = 1; // elements of R known to be < l_0

    while llen!() > 1 && rlen!() > highwater {
        let xlen = gallop_right(&s[left], &s[split + highwater .. right], cmpleftright) + highwater;
        if xlen == rlen!() {
            break
        }
        // find Z in L where Z[i] < R'[0]
        // - Since L[max] > R[max], exclude L[max] from search
        // - Since R[split + xlen] > L[0] from previous search, exclude L[0] from search
        // - this search relies on invariant |L| > 1, tested in loop condition
        let zlen = gallop_right(&s[split + xlen], &s[left + 1 .. split - 1], cmprightleft) + 1;

        if llen!() <= xlen + zlen {
            rotate(&mut s[left .. split + xlen], xlen);
            left += xlen + zlen;
            split += xlen;
            highwater = 1;
        } else if zlen < xlen {
            swap_ends(&mut s[left .. split + zlen], zlen);
            rotate(&mut s[split .. split + xlen], xlen - zlen);
            left += zlen;
            highwater = xlen + 1;
        } else {
            swap_ends(&mut s[left + zlen - xlen .. split + xlen], xlen);
            rotate(&mut s[left .. left + zlen], xlen);
            left += zlen;
            highwater = xlen + 1;
        }
    }
    // since r_0..r_highwater are < l_0, we just need to swap L and R
    // since l_max is largest value, if |L| = 1, we just need to swap L and R
    rotate(&mut s[left .. right], rlen!());
}

fn rotate_right_1<T>(s: &mut [T]) {
    debug_assert!(s.len() > 1);
    let r = s.len() - 1;
    unsafe {
        let src = s.as_ptr();
        let dst = s.as_mut_ptr();
        let mut tmp: T = std::mem::uninitialized();
        std::ptr::copy_nonoverlapping(src.offset(r as isize), &mut tmp, 1);
        std::ptr::copy(src, dst.offset(1), r);
        std::ptr::copy_nonoverlapping(&tmp, dst, 1);
        std::mem::forget(tmp);
    }
}

fn sort4<T, F>(s: &mut [T], compare: &F)
where
    F: Fn(&T, &T) -> Ordering
{
    // Handcrafted sort for chunks of 4
    debug_assert!(s.len() == 4);
    if compare(&s[0], &s[1]) == Ordering::Greater {
        s.swap(0, 1);
    }
    if compare(&s[1], &s[2]) == Ordering::Greater {
        if compare(&s[0], &s[2]) == Ordering::Greater {
            rotate_right_1(&mut s[0 .. 3]);
        } else {
            s.swap(1, 2);
        }
    }
    if compare(&s[1], &s[3]) == Ordering::Greater {
        if compare(&s[0], &s[3]) == Ordering::Greater {
            rotate_right_1(s);
        } else {
            rotate_right_1(&mut s[1 ..]);
        }
    } else if compare(&s[2], &s[3]) == Ordering::Greater {
        s.swap(2, 3);
    }
}

fn sort3<T, F>(s: &mut [T], compare: &F)
where
    F: Fn(&T, &T) -> Ordering
{
    // Handcrafted sort for chunks of 3
    debug_assert!(s.len() == 3);
    if compare(&s[0], &s[1]) == Ordering::Greater {
        s.swap(0, 1);
    }
    if compare(&s[1], &s[2]) == Ordering::Greater {
        if compare(&s[0], &s[2]) == Ordering::Greater {
            rotate_right_1(&mut s[0 .. 3]);
        } else {
            s.swap(1, 2);
        }
    }
}

fn sort2<T, F>(s: &mut [T], compare: &F)
where
    F: Fn(&T, &T) -> Ordering
{
    // Handcrafted sort for chunks of 2
    debug_assert!(s.len() == 2);
    if compare(&s[0], &s[1]) == Ordering::Greater {
        s.swap(0, 1);
    }
}

fn sort_by_ordering<T, F, G>(s: &mut [T], cmpleftright: &F, cmprightleft: &G, recurse: u32)
where
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    // Move backwards through the slice, sorting blocks of 4. When we have two sorted blocks,
    // merge them into a block of 8.  When we have two sorted blocks of 8, merge them into a
    // block of 16.  To do this, look at the start of each 4-block.  If it has a 0 in the 4's digit
    // (0100), then it is an even block of 4 - add it to the following odd block of 4. Then check
    // the 8's digit (1000). If it is an even block of 8, add it to the following odd block of 8.
    // We check for the end of the slice, to avoid merging an even block into a non-existent block.
    // We do this to be cache-friendly rather than sorting by 4's, then 8's, etc. reading the
    // entire slice each time.
    let end = s.len();
    let rump = end % 4;
    let mut start = end - rump;
    match rump {
        0 | 1 => (),
        2 => sort2(&mut s[start ..], cmpleftright),
        3 => sort3(&mut s[start ..], cmpleftright),
        _ => unreachable!(),
    }

    while start > 0 {
        let mut end = start;
        start -= 4;
        sort4(&mut s[start .. end], cmpleftright);
        let mut size = 4usize;
        while start & size == 0 && end < s.len() {
            end = min(end + size, s.len());
            merge(&mut s[start .. end], size, cmpleftright, cmprightleft, recurse);
            size *= 2;
        }
    }
}

pub fn sort_by<T, F>(s: &mut [T], compare: &F)
where
    F: Fn(&T, &T) -> Ordering
{
    sort_by_ordering(
        s,
        &|ref a, ref b|{compare(&a, &b).then(Ordering::Less)},
        &|ref a, ref b|{compare(&a, &b).then(Ordering::Greater)},
        RECURSION_LIMIT
    )
}

pub fn sort<T>(s: &mut [T])
where
    T: Ord
{
    sort_by(s, &T::cmp);
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::cmp::Ordering;

    // A non-copy but comparable type is useful for testing, as bad moves are hidden by Copy types.
    #[derive(PartialEq,Eq,PartialOrd,Ord,Debug)]
    struct Nc(i32);

    #[test]
    fn add_modulo_lt_n() {
        assert_eq!(super::add_modulo(5, 6, 15), 11);
    }

    #[test]
    fn add_modulo_eq_n() {
        assert_eq!(super::add_modulo(9, 6, 15), 0);
    }

    #[test]
    fn add_modulo_gt_n() {
        assert_eq!(super::add_modulo(12, 6, 15), 3);
    }

    #[test]
    fn addmod_no_overflow() {
        let max = i32::max_value();
        assert_eq!(super::add_modulo(max - 1, max - 1, max), max - 2);
    }

    #[test]
    fn sort_0() {
        let mut s: [i32; 0] = [];
        super::sort(&mut s);
    }

    #[test]
    fn sort_1() {
        let mut s = [5];
        super::sort(&mut s);
        assert_eq!(s[0], 5);
    }

    #[test]
    fn sort_2_ordered() {
        let mut s = [1, 2];
        super::sort(&mut s);
        assert_eq!(s[0], 1);
        assert_eq!(s[1], 2);
    }

    #[test]
    fn sort_2_unordered() {
        let mut s = [2, 1];
        super::sort(&mut s);
        assert_eq!(s[0], 1);
        assert_eq!(s[1], 2);
    }

    #[test]
    fn sort_ordered() {
        let mut s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let count = Cell::new(0);
        super::sort_by(&mut s, &|a: &usize, b: &usize|{count.set(count.get() + 1); a.cmp(&b)});
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i);
        }
        // Using the merge algorithm only gives the minimum number of comparisons (15).  However,
        // the handcrafted sort of 4 uses one additional comparison for each block of 4.  This
        // benefits random data more, and sort of ordered data is still faster than anything else.
        assert_eq!(count.get(), 19); // minimum is 15
    }

    #[test]
    fn sort_reverse() {
        let mut s = [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0];
        super::sort(&mut s);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i);
        }
    }

    #[test]
    fn sort_mod3() {
        let mut s = [0, 3, 6, 9, 12, 15, 1, 4, 7, 10, 13, 2, 5, 8, 11, 14];
        super::sort(&mut s);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i);
        }
    }

    #[test]
    fn sort_equal() {
        let mut s = [5, 5, 5, 5, 5, 5, 5, 5, 5];
        super::sort(&mut s);
        for elem in s.iter() {
            assert_eq!(*elem, 5);
        }
    }

    #[test]
    fn merge_0() {
        let mut s: [i32; 0] = [];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge(&mut s, 0, &compare, &compare, super::MAX_RECURSION_LIMIT);
        assert_eq!(count.get(), 0);
    }

    #[test]
    fn merge_0_1() {
        let mut s = [1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge(&mut s, 0, &compare, &compare, super::MAX_RECURSION_LIMIT);
        assert_eq!(count.get(), 0);
        assert_eq!(s[0], 1);
    }

    #[test]
    fn merge_1_0() {
        let mut s = [1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge(&mut s, 1, &compare, &compare, super::MAX_RECURSION_LIMIT);
        assert_eq!(count.get(), 0);
        assert_eq!(s[0], 1);
    }

    #[test]
    fn merge_1_1_ordered() {
        let mut s = [1, 2];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge(&mut s, 1, &compare, &compare, super::MAX_RECURSION_LIMIT);
        assert_eq!(count.get(), 1);
        assert_eq!(s[0], 1);
        assert_eq!(s[1], 2);
    }

    #[test]
    fn merge_1_1_unordered() {
        let mut s = [2, 1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge(&mut s, 1, &compare, &compare, super::MAX_RECURSION_LIMIT);
        // One compare required, but there are 2 debug_assert that compare
        assert!(count.get() <= 3);
        assert_eq!(s[0], 1);
        assert_eq!(s[1], 2);
    }

    #[test]
    fn merge_1_n() {
        let mut s = [7, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10];
        let count = Cell::new(0);
        let compare = |a: &usize, b: &usize|{count.set(count.get() + 1); usize::cmp(&a, &b)};
        super::merge(&mut s, 1, &compare, &compare, super::MAX_RECURSION_LIMIT);
        // assert_eq!(count.get(), 4);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i);
        }
    }

    #[test]
    fn merge_n_1() {
        let mut s = [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 7];
        let count = Cell::new(0);
        let leftlen = s.len() - 1;
        let compare = |a: &usize, b: &usize|{count.set(count.get() + 1); usize::cmp(&a, &b)};
        super::merge(&mut s, leftlen, &compare, &compare, super::MAX_RECURSION_LIMIT);
        // assert_eq!(count.get(), 5);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i);
        }
    }

    #[test]
    fn merge_ordered() {
        let mut s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let count = Cell::new(0);
        let leftlen = s.len() / 2;
        let compare = |a: &usize, b: &usize|{count.set(count.get() + 1); usize::cmp(&a, &b)};
        super::merge(&mut s, leftlen, &compare, &compare, super::MAX_RECURSION_LIMIT);
        assert_eq!(count.get(), 1);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i);
        }
    }

    #[test]
    fn merge_alternative() {
        let mut s = [
            Nc(0), Nc(2), Nc(4), Nc(6), Nc(8), Nc(10), Nc(12), Nc(14),
            Nc(1), Nc(3), Nc(5), Nc(7), Nc(9), Nc(11), Nc(13), Nc(15)
        ];
        let leftlen = s.len() / 2;
        super::merge(&mut s, leftlen, &Nc::cmp, &Nc::cmp, super::MAX_RECURSION_LIMIT);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, Nc(i as i32));
        }
    }

    #[test]
    fn gallop_right_0() {
        assert_eq!(super::gallop_right(&Nc(3), &[], &Nc::cmp), 0)
    }

    #[test]
    fn gallop_right_1_before() {
        assert_eq!(super::gallop_right(&Nc(1), &[Nc(2)], &Nc::cmp), 0)
    }
    #[test]
    fn gallop_right_1_after() {
        assert_eq!(super::gallop_right(&Nc(3), &[Nc(2)], &Nc::cmp), 1)
    }

    #[test]
    fn gallop_right_2_before() {
        assert_eq!(super::gallop_right(&Nc(1), &[Nc(2), Nc(4)], &Nc::cmp), 0)
    }
    #[test]
    fn gallop_right_2_middle() {
        assert_eq!(super::gallop_right(&Nc(3), &[Nc(2), Nc(4)], &Nc::cmp), 1)
    }
    #[test]
    fn gallop_right_2_after() {
        assert_eq!(super::gallop_right(&Nc(5), &[Nc(2), Nc(4)], &Nc::cmp), 2)
    }

    #[test]
    fn gallop_right_3_before() {
        assert_eq!(super::gallop_right(&Nc(1), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp), 0)
    }
    #[test]
    fn gallop_right_3_lt() {
        // Default to Ordering::Less if the value should be inserted before equal values
        let compare = |a: &Nc, b: &Nc|{Nc::cmp(&a, &b).then(Ordering::Less)};
        assert_eq!(super::gallop_right(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &compare), 1)
    }
    #[test]
    fn gallop_right_3_le() {
        // Default to Ordering::Greater if value should be inserted after equal values
        let compare = |a: &Nc, b: &Nc|{Nc::cmp(&a, &b).then(Ordering::Greater)};
        assert_eq!(super::gallop_right(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &compare), 2)
    }
    #[test]
    fn gallop_right_3_after() {
        assert_eq!(super::gallop_right(&Nc(7), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp), 3)
    }

    #[test]
    fn gallop_right_2powm1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::gallop_right(&v, &s, &|&a, &b|{count.set(count.get() + 1); usize::cmp(&a, &b).then(Ordering::Less)}), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![2, 2, 3, 3, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6])
    }

    #[test]
    fn gallop_right_2pow() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::gallop_right(&v, &s, &|&a, &b|{count.set(count.get() + 1); usize::cmp(&a, &b).then(Ordering::Less)}), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![2, 2, 3, 3, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 4])
    }

    #[test]
    fn gallop_right_2powp1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::gallop_right(&v, &s, &|&a, &b|{count.set(count.get() + 1); usize::cmp(&a, &b).then(Ordering::Less)}), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![2, 2, 3, 3, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 5, 5   ])
    }

    #[test]
    fn gallop_right_20() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::gallop_right(&v, &s, &|&a, &b|{count.set(count.get() + 1); usize::cmp(&a, &b).then(Ordering::Less)}), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![2, 2, 3, 3, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6])
    }

    #[test]
    fn binary_search_0() {
        assert_eq!(super::binary_search(&Nc(3), &[], &Nc::cmp), 0)
    }

    #[test]
    fn binary_search_1_before() {
        assert_eq!(super::binary_search(&Nc(1), &[Nc(2)], &Nc::cmp), 0)
    }
    #[test]
    fn binary_search_1_after() {
        assert_eq!(super::binary_search(&Nc(3), &[Nc(2)], &Nc::cmp), 1)
    }

    #[test]
    fn binary_search_2_before() {
        assert_eq!(super::binary_search(&Nc(1), &[Nc(2), Nc(4)], &Nc::cmp), 0)
    }
    #[test]
    fn binary_search_2_middle() {
        assert_eq!(super::binary_search(&Nc(3), &[Nc(2), Nc(4)], &Nc::cmp), 1)
    }
    #[test]
    fn binary_search_2_after() {
        assert_eq!(super::binary_search(&Nc(5), &[Nc(2), Nc(4)], &Nc::cmp), 2)
    }

    #[test]
    fn binary_search_3_before() {
        assert_eq!(super::binary_search(&Nc(1), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp), 0)
    }
    #[test]
    fn binary_search_3_lt() {
        // Default to Ordering::Less if the value should be inserted before equal values
        let compare = |a: &Nc, b: &Nc|{Nc::cmp(&a, &b).then(Ordering::Less)};
        assert_eq!(super::binary_search(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &compare), 1)
    }
    #[test]
    fn binary_search_3_le() {
        // Default to Ordering::Greater if value should be inserted after equal values
        let compare = |a: &Nc, b: &Nc|{Nc::cmp(&a, &b).then(Ordering::Greater)};
        assert_eq!(super::binary_search(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &compare), 2)
    }
    #[test]
    fn binary_search_3_after() {
        assert_eq!(super::binary_search(&Nc(7), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp), 3)
    }

    #[test]
    fn binary_search_2powm1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::binary_search(&v, &s, &|&a, &b|{count.set(count.get() + 1); usize::cmp(&a, &b).then(Ordering::Less)}), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4])
    }

    #[test]
    fn binary_search_stable() {
        let s = [1, 5, 5, 5, 5, 5, 8];
        let count = Cell::new(0);
        super::binary_search(&5, &s, &|&a, &b|{count.set(count.get() + 1); i32::cmp(&a, &b).then(Ordering::Less)});
        assert_eq!(count.get(), 3);
    }

    #[test]
    fn binary_search_unstable() {
        // If compare can return Equal, then insertion point returned on first match
        // Since first comparsion finds matching value, it will return immediately.
        let s = [1, 5, 5, 5, 5, 5, 8];
        let count = Cell::new(0);
        super::binary_search(&5, &s, &|&a, &b|{count.set(count.get() + 1); i32::cmp(&a, &b)});
        assert_eq!(count.get(), 1);
    }

    #[test]
    fn swap_ends_adjacent() {
        let mut buf = [1, 2, 3, 4, 5, 6];
        super::swap_ends(&mut buf, 3);
        assert_eq!(buf, [4, 5, 6, 1, 2, 3]);
    }

    #[test]
    fn swap_ends_disjoint() {
        let mut buf = [1, 2, 3, 4, 5, 6];
        super::swap_ends(&mut buf[1..6], 2);
        assert_eq!(buf, [1, 5, 6, 4, 2, 3]);
    }

    #[test]
    fn swap_ends_zero() {
        let mut buf = [1, 2, 3, 4, 5, 6];
        super::swap_ends(&mut buf, 0);
        assert_eq!(buf, [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn rotate0_0() {
        let mut buf: [i32; 0] = [];
        super::rotate(&mut buf, 0);
        assert_eq!(buf, []);
    }

    #[test]
    fn rotate0_1() {
        let mut buf = [4];
        super::rotate(&mut buf, 0);
        assert_eq!(buf, [4]);
    }

    #[test]
    fn rotate1_0() {
        let mut buf = [4];
        super::rotate(&mut buf, 1);
        assert_eq!(buf, [4]);
    }

    #[test]
    fn rotate1_1() {
        let mut buf = [5, 4];
        super::rotate(&mut buf, 1);
        assert_eq!(buf, [4, 5]);
    }

    #[test]
    fn rotate_gcd_1() {
        let mut buf = [5, 4, 3, 2, 1];
        super::rotate(&mut buf, 2);
        assert_eq!(buf, [2, 1, 5, 4, 3]);
    }

    #[test]
    fn rotate_gcd_3() {
        let mut buf = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21];
        super::rotate(&mut buf, 6);
        assert_eq!(buf, [16, 17, 18, 19, 20, 21, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
    }

    quickcheck! {
        fn sort_i32(vec: Vec<i32>) -> bool {
            let mut s = vec.clone();
            super::sort(&mut s);
            s.windows(2).all(|v| v[0] <= v[1])
        }

        fn sort_char(vec: Vec<char>) -> bool {
            let mut s = vec.clone();
            super::sort(&mut s);
            s.windows(2).all(|v| v[0] <= v[1])
        }

        fn sort_str(vec: Vec<String>) -> bool {
            let mut s = vec.clone();
            super::sort(&mut s);
            s.windows(2).all(|v| v[0] <= v[1])
        }
    }
}
