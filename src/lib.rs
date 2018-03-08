#![feature(stmt_expr_attributes)]
#![feature(swap_nonoverlapping)]
#![feature(pointer_methods)]

extern crate gcd;

use std::cmp::min;
use std::cmp::Ordering;

use gcd::Gcd;

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

macro_rules! debug {
    ($( $arg:expr ),*) => (if cfg!(debug_assertions) { println!($($arg),*) })
}

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
    let mut interval = 1;
    let mut trial = lo;
    while interval < length - trial {
        trial += interval;
        match compare(value, &buffer[trial]) {
            Ordering::Less => {
                hi = trial;
                break;
            },
            Ordering::Greater => {
                lo = trial + 1;
                interval *= 2;
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
    binary_search(value, &buffer[.. hi], lo, compare)
}

fn gallop_left<T, F>(value: &T, buffer: &[T], compare: &F) -> usize
where
    F: Fn(&T, &T) -> Ordering
{
    // like gallop_right, but start from the end of the sequence.  There is a slight difference
    // in that when length == 2^n then `interval < trial` does not examine the far end before
    // dropping to binary search.  This doesn't appear to make much difference in practice.
    let length = buffer.len();
    let mut lo = 0;       // lowest candidate
    let mut hi = length;  // highest candidate

    if buffer.is_empty() {
        return 0;
    }
    let mut interval = 1;
    let mut trial = hi - 1;
    while interval < trial {
        trial -= interval;
        match compare(value, &buffer[trial]) {
            Ordering::Less => {
                hi = trial;
                interval *= 2;
            },
            Ordering::Greater => {
                lo = trial + 1;
                break;
            },
            Ordering::Equal => {
                #![cold]
                return trial;
            }
        }
    }

    // At this point, either lo == 0, and we're processing the rump of the sequence, or
    // lo-hi contains 2^n - 1 elements containing the correct position.  2^n - 1 elements gives us
    // a balanced binary tree.  Perform binary search to find the final insertion position.
    debug_assert!(lo == 0 || (hi - lo + 1).is_power_of_two());
    binary_search(value, &buffer[.. hi], lo, compare)
}

fn binary_search<T, F>(value: &T, buffer: &[T], start: usize, compare: &F) -> usize
where
    F: Fn(&T, &T) -> Ordering
{
    let length = buffer.len();
    let mut lo = start;   // lowest candidate
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
    debug_assert!(k > 0);
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

macro_rules! stack_slice_max {
    ( $type:ty ) => {
        STACK_OBJECT_SIZE / std::mem::size_of::<T>()
    };
}

macro_rules! stack_slice_unsafe {
    ( [ $type:ty ; $len:expr ] ) => {{
        // size_of cannot be used to size an array: https://github.com/rust-lang/rust/issues/43408
        // let mut tmp: [T; STACK_OBJECT_SIZE / std::mem::size_of::<T>()] = std::mem::uninitialized();
        // There's no way to express alignment: https://github.com/rust-lang/rfcs/issues/325
        // let mut tmp: [u8; STACK_OBJECT_SIZE] = std::mem::uninitialized();
        // Using primitive non-Drop types also means we don't need to mem::forget or ManuallyDrop
        // So, using u64 to improve alignment, this seems to be the best we can do right now:
        debug_assert!($len * std::mem::size_of::<$type>() <= STACK_OBJECT_SIZE);
        let mut tmp: [u64; STACK_OBJECT_SIZE / 8] = std::mem::uninitialized();
        tmp
    }};
}

fn rotate_left_shift<T>(s: &mut [T], llen: usize) {
    let rlen = s.len() - llen;
    unsafe {
        let mut tmp = stack_slice_unsafe!([T; llen]);
        let t = tmp.as_mut_ptr() as *mut T;
        let src = s.as_ptr();
        let dst = s.as_mut_ptr();
        std::ptr::copy_nonoverlapping(src, t, llen);
        std::ptr::copy(src.offset(llen as isize), dst, rlen);
        std::ptr::copy_nonoverlapping(t, dst.offset(rlen as isize), llen);
    }
}

fn rotate_right_shift<T>(s: &mut [T], rlen: usize) {
    let llen = s.len() - rlen;
    unsafe {
        let mut tmp = stack_slice_unsafe!([T; rlen]);
        let t = tmp.as_mut_ptr() as *mut T;
        let src = s.as_ptr();
        let dst = s.as_mut_ptr();
        std::ptr::copy_nonoverlapping(src.offset(llen as isize), t, rlen);
        std::ptr::copy(src, dst.offset(rlen as isize), llen);
        std::ptr::copy_nonoverlapping(t, dst, rlen);
    }
}

fn rotate<T>(s: &mut [T], rlen: usize) {
    // Rotate the last rlen elements to the front of the slice.
    // given a slice of 0..n, move n-rlen..n to front and 0..n-rlen to end
    debug_assert!(rlen > 0);
    let llen = s.len() - rlen;
    debug_assert!(llen > 0);
    match llen.cmp(&rlen) {
        Ordering::Less => {
            if llen <= stack_slice_max!(T) {
                rotate_left_shift(s, llen);
                return
            }
        },
        Ordering::Greater => {
            if rlen <= stack_slice_max!(T) {
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


fn trim<T, F, G>(l: &[T], r: &[T], cmpleftright: &F, cmprightleft: &G) -> Option<(usize, usize)>
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
    // Then, a gallop left of the l[max] value over R is done, as any values in R that are higher
    // than l[max] are already in their final position, and can be ignored.
    //
    // Finally, we check for values in L that are less than r[0], as they are also in their final
    // position.  In this case, we gallop right, since we expect r[0] to be lower than the median
    // value in L.

    if l.is_empty() || r.is_empty() {
        return None;
    }

    // Check if sequences are already in order
    if cmpleftright(l.last().unwrap(), r.first().unwrap()) != Ordering::Greater {
        // l[max] <= r[0] -> L-R is already sorted
        return None;
    }
    // Find insertion point of l[max] in R and trim off higher values, which are in final position,
    // leaving l[max] as highest value.  From above, l[max] > r[0], so exclude r[0] from search.
    let right = gallop_left(l.last().unwrap(), &r[1..], cmpleftright) + 1;

    // Find insertion point of r[0] in L and trim off lower values, which are in final position,
    // leaving r[0] as lowest value.  From above, l[max] > r[0], so exclude r[0] from search.
    let left = gallop_right(r.first().unwrap(), &l[.. l.len() - 1], cmprightleft);

    Some((left, right))
}

fn merge_inplace<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G, recurse: u32)
where
    T: std::fmt::Debug,
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    if let Some((left, right)) = trim(&s[..split], &s[split..], cmpleftright, cmprightleft) {
        debug!("\nS={:?}", s);
        merge_trimmed(&mut s[left .. split + right], split - left, cmpleftright, cmprightleft, recurse);
        debug!("S={:?}\n", s);
    }
}

fn merge_trimmed<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G, recurse: u32)
where
    T: std::fmt::Debug,
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    macro_rules! llen {() => (split)}
    macro_rules! rlen {() => (s.len() - split)}

    if stack_slice_max!(T) > 1 && llen!() <= stack_slice_max!(T) {
        merge_left(s, split, cmpleftright, cmprightleft);
    } else if stack_slice_max!(T) > 1 && rlen!() <= stack_slice_max!(T) {
        merge_right(s, split, cmpleftright, cmprightleft);
    } else if recurse == 0 {
        merge_final(s, split, cmpleftright, cmprightleft);
    } else {
        merge_recurse(s, split, cmpleftright, cmprightleft, recurse - 1);
    }
}

// When dropped, copies from `src` into `dest`. Derived from
// https://github.com/rust-lang/rust/blob/27a046e/src/liballoc/slice.rs#L2021-L2031
struct CopyOnDrop<T> {
    src: *const T,
    dest: *mut T,
    len: usize,
}

impl<T> Drop for CopyOnDrop<T> {
    fn drop(&mut self) {
        unsafe {
            std::ptr::copy_nonoverlapping(self.src, self.dest, self.len);
        }
    }
}

fn merge_left<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G)
where
    T: std::fmt::Debug,
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    // Perform a merge by moving the left side of the merge to a stack slice, and then
    // merging it and the right towards the left side of the original buffer.

    // 1. |L| > 0
    debug_assert!(split > 0);
    // 2. |R| > 0
    debug_assert!(s.len() - split > 0);
    // 3. l_max is max value
    debug_assert!(cmprightleft(s.last().unwrap(), &s[split - 1]) == Ordering::Less);
    // 4. r_0 is min value
    debug_assert!(cmpleftright(s.first().unwrap(), &s[split]) == Ordering::Greater);
    unsafe {
        let mut tmp = stack_slice_unsafe!([T; split]);
        std::ptr::copy_nonoverlapping(s.as_ptr(), tmp.as_mut_ptr() as *mut T, split);
        let mut l = std::slice::from_raw_parts(tmp.as_ptr() as *const T, split);
        let mut hole = CopyOnDrop {src: l.as_ptr(), dest: s.as_mut_ptr(), len: l.len()};
        let mut r = &s[split ..];
        debug!("merge_left S {:?} H {:?} R {:?} / L {:?}", &s[..s.len()-r.len()-hole.len], &s[s.len()-r.len()-hole.len..s.len()-r.len()], r, l);
        while l.len() > 1 {
            let xlen = gallop_right(&l[0], &r[1 ..], cmpleftright) + 1;
            if xlen == r.len() {
                break;
            }
            let zlen = gallop_right(&r[xlen], &l[1 .. l.len() - 1], cmprightleft) + 1;
            std::ptr::copy(r.as_ptr(), hole.dest, xlen);
            r = &r[xlen ..];
            hole.dest = hole.dest.add(xlen);
            std::ptr::copy_nonoverlapping(l.as_ptr(), hole.dest, zlen);
            l = &l[zlen ..];
            hole.src = l.as_ptr();
            hole.dest = hole.dest.add(zlen);
            hole.len -= zlen;
            debug!("merge_left S {:?} - H {:?} - R {:?} / L {:?}", &s[..s.len()-r.len()-hole.len], &s[s.len()-r.len()-hole.len..s.len()-r.len()], r, l);
        }
        debug_assert!(r.len() > 0);
        debug_assert!(l.len() > 0);
        std::ptr::copy(r.as_ptr(), hole.dest, r.len());
        hole.dest = hole.dest.add(r.len());
        // When `hole` is dropped, it will copy the last section on the stack slice to end of `s`
    }
}

fn merge_right<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G)
where
    T: std::fmt::Debug,
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    // Perform a merge by moving the right side of the merge to a stack slice, and then
    // merging it and the left towards the right side of the original buffer.

    // 1. |L| > 0
    debug_assert!(split > 0);
    // 2. |R| > 0
    debug_assert!(s.len() - split > 0);
    // 3. l_max is max value
    debug_assert!(cmprightleft(s.last().unwrap(), &s[split - 1]) == Ordering::Less);
    // 4. r_0 is min value
    debug_assert!(cmpleftright(s.first().unwrap(), &s[split]) == Ordering::Greater);
    unsafe {
        let rlen = s.len() - split;
        let mut tmp = stack_slice_unsafe!([T; rlen]);
        std::ptr::copy_nonoverlapping(s.as_ptr().add(split), tmp.as_mut_ptr() as *mut T, rlen);
        let mut r = std::slice::from_raw_parts(tmp.as_ptr() as *const T, rlen);
        let mut hole = CopyOnDrop {src: r.as_ptr(), dest: s.as_mut_ptr().add(split), len: r.len()};
        let mut l = &s[.. split];
        debug!("merge_right L {:?} - H {:?} - S {:?} / R {:?}", l, &s[l.len()..l.len()+hole.len], &s[l.len()+hole.len..], r);
        while r.len() > 1 {
            let xlen = l.len() - gallop_left(r.last().unwrap(), &l[.. l.len() - 1], cmprightleft);
            if xlen == l.len() {
                break;
            }
            let zlen = r.len() - (gallop_left(&l[l.len() - xlen - 1], &r[1 .. r.len() - 1], cmpleftright) + 1);
            hole.dest = hole.dest.sub(xlen);
            std::ptr::copy(l.as_ptr().add(l.len() - xlen), hole.dest.add(hole.len), xlen);
            l = &l[.. l.len() - xlen];
            hole.len -= zlen;
            std::ptr::copy_nonoverlapping(r.as_ptr().add(r.len() - zlen), hole.dest.add(hole.len), zlen);
            r = &r[.. r.len() - zlen];
            debug!("merge_right L {:?} - H {:?} - S {:?} / R {:?}", l, &s[l.len()..l.len()+hole.len], &s[l.len()+hole.len..], r);
        }
        debug_assert!(l.len() > 0);
        debug_assert!(r.len() > 0);
        hole.dest = hole.dest.sub(l.len());
        std::ptr::copy(l.as_ptr(), hole.dest.add(hole.len), l.len());
        // When `hole` is dropped, it will copy the last section on the stack slice to end of `s`
    }
}

fn merge_recurse<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G, recurse: u32)
where
    T: std::fmt::Debug,
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

    debug!("merge_recurse S {:?} - L {:?} - M {:?} - R {:?}", &s[..left], &s[left..split], &s[split..split+highwater], &s[split+highwater..]);
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
            if zlen != xlen {
                rotate(&mut s[left .. left + zlen], xlen);
            }
            left += zlen;
            highwater = xlen + 1;
        }
        debug!("merge_recurse S {:?} - L {:?} - M {:?} - R {:?}", &s[..left], &s[left..split], &s[split..split+highwater], &s[split+highwater..]);
    }
    // since r_0..r_highwater are < l_0, we just need to swap L and R
    // since l_max is largest value, if |L| = 1, we just need to swap L and R
    rotate(&mut s[left .. right], rlen!());
}

fn merge_final<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G)
where
    T: std::fmt::Debug,
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

    debug!("merge_final S {:?} - L {:?} - M {:?} - R {:?}", &s[..left], &s[left..split], &s[split..split+highwater], &s[split+highwater..]);
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
            if zlen != xlen {
                rotate(&mut s[left .. left + zlen], xlen);
            }
            left += zlen;
            highwater = xlen + 1;
        }
        debug!("merge_final S {:?} - L {:?} - M {:?} - R {:?}", &s[..left], &s[left..split], &s[split..split+highwater], &s[split+highwater..]);
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
        let tmp = std::ptr::read(src.add(r));
        std::ptr::copy(src, dst.add(1), r);
        std::ptr::write(dst, tmp);
    }
}

macro_rules! ascending {
    ( $comparison:expr ) => ( $comparison != Ordering::Greater )
}

fn sort4<T, F>(s: &mut [T], compare: &F) -> bool
where
    T: std::fmt::Debug,
    F: Fn(&T, &T) -> Ordering
{
    // Handcrafted sort for chunks of 4
    //
    // We'd like to optimise ascending and descending sequences to 3 comparisons, and minimise
    // comparisons for other patterns.
    //
    // To do this, we need to change path depending on whether the block appears to be ascending
    // or descending.  We check elements 0 and 1, then choose a path, compare elements 1 and 2,
    // and refine the path. If we have a purely ascending or descending sequence after two
    // comparisons, then we do the third comparison to check that it continues.  Otherwise, we
    // resort to sorting  based on what we've learnt.  This sort uses 5 comparisons max, which is
    // pretty good. The theoretical minimum is log2(24) = 4.585. With 2 patterns requiring 3
    // comparisons and 2 requiring 4 comparisons, this algorithm averages 4.75 comparisons.
    //
    // However, the bias towards ascending and descending sequences gives it a small penalty for
    // random sequences over the previous algorithm, which was insertion sort hard-wired for
    // a block of 4.
    //
    // This function also returns a boolean which indicates if the block is mostly descending.
    // This can be used for further optimisation at a higher level.
    assert!(s.len() == 4);
    debug!("sort4 in {:?}", s);
    if ascending!(compare(&s[0], &s[1])) {
        if ascending!(compare(&s[1], &s[2])) {
            // 1234 1243 1342 2341
            if ! ascending!(compare(&s[2], &s[3])) {
                // 1243 1342 2341
                if ascending!(compare(&s[0], &s[3])) {
                    // 1243 1342
                    if ascending!(compare(&s[1], &s[3])) {
                        // 1243
                        s.swap(2, 3);
                    } else {
                        // 1342
                        rotate_right_1(&mut s[1..]);
                    }
                } else {
                    // 2341
                    rotate_right_1(s);
                }
            }
            // 1234 = 3
            // 2341 = 4
            // 1243 1342 = 5
            debug!("sort4 {:?}", s);
            false
        } else {
            // 1324 1423 1432 2314
            // 2413 2431 3412 3421
            if ! ascending!(compare(&s[0], &s[2])) {
                //
                s.swap(0, 2);
            }
            // 1324(1324) 1423(1423) 1432(1432) 1324(2314)
            // 1423(2413) 2431(2431) 1432(3412) 2431(3421)
            if ascending!(compare(&s[2], &s[3])) {
                // 1324(1324) 1423(1423) 1324(2314) 1423(2413)
                if ! ascending!(compare(&s[1], &s[3])) {
                    s.swap(1, 3);
                }
                // 1324(1324) 1324(1423) 1324(2314) 1324(2413)
                s.swap(1, 2);
                debug!("sort4 {:?}", s);
                false
            } else {
                // 1432(1432) 2431(2431) 1432(3412) 2431(3421)
                if ! ascending!(compare(&s[0], &s[3])) {
                    // 2431(2431) 2431(3421)
                    s.swap(0, 3);
                }
                // 1432(1432) 1432(2431) 1432(3412) 1432(3421)
                s.swap(1, 3);
                debug!("sort4 {:?}", s);
                true
            }
            // 1324 1423 1432 2314 2413 2431 3412 3421 = 5
        }
    } else {
        if ! ascending!(compare(&s[1], &s[2])) {
            // 3214 4213 4312 4321
            if ascending!(compare(&s[2], &s[3])) {
                // 3214 4213 4312
                s.swap(0, 2);
                // 1234(3214) 1243(4213) 1342(4312)
                if ! ascending!(compare(&s[2], &s[3])) {
                    // 1243(4213) 1342(4312)
                    s.swap(2, 3);
                    // 1234(4213) 1324(4312)
                    if ! ascending!(compare(&s[1], &s[2])) {
                        // 1324(4312)
                        s.swap(1, 2);
                    }
                }
            } else {
                // 4321
                s.swap(0, 3);
                s.swap(1, 2);
            }
            debug!("sort4 {:?}", s);
            true
            // 4321 = 3
            // 3214 = 4
            // 4213 4312 = 5
        } else {
            // 2134 2143 3124 3142
            // 3241 4123 4132 4231
            if ! ascending!(compare(&s[0], &s[2])) {
                s.swap(0, 2);
            }
            // 2134(2134) 2143(2143) 2134(3124) 3142(3142)
            // 3241(3241) 2143(4123) 3142(4132) 3241(4231)
            if ascending!(compare(&s[0], &s[3])) {
                // 2134(2134) 2143(2143) 2134(3124) 2143(4123)
                if ! ascending!(compare(&s[2], &s[3])) {
                    // 2143(2143) 2143(4123)
                    s.swap(2, 3);
                }
                s.swap(0, 1);
                debug!("sort4 {:?}", s);
                false
            } else {
                // 3142(3142) 3241(3241) 3142(4132) 3241(4231)
                if ascending!(compare(&s[1], &s[3])) {
                    s.swap(1, 3);
                }
                // 3241(3142) 3241(3241) 3241(4132) 3241(4231)
                s.swap(2, 3);
                // 3214(3142) 3214(3241) 3214(4132) 3214(4231)
                s.swap(0, 2);
                debug!("sort4 {:?}", s);
                false
            }
            // 2134 2143 3124 3142 3241 4123 4132 4231 = 5
        }
    }
}

fn sort3<T, F>(s: &mut [T], compare: &F)
where
    F: Fn(&T, &T) -> Ordering
{
    // Handcrafted sort for chunks of 3
    assert!(s.len() == 3);
    if ! ascending!(compare(&s[0], &s[1])) {
        s.swap(0, 1);
    }
    if ! ascending!(compare(&s[1], &s[2])) {
        if ascending!(compare(&s[0], &s[2])) {
            s.swap(1, 2);
        } else {
            rotate_right_1(&mut s[.. 3]);
        }
    }
}

fn sort2<T, F>(s: &mut [T], compare: &F)
where
    F: Fn(&T, &T) -> Ordering
{
    // Handcrafted sort for chunks of 2
    assert!(s.len() == 2);
    if ! ascending!(compare(&s[0], &s[1])) {
        s.swap(0, 1);
    }
}

fn sort_by_ordering<T, F, G>(s: &mut [T], cmpleftright: &F, cmprightleft: &G, recurse: u32)
where
    T: std::fmt::Debug,
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    let end = s.len();
    let rump = end % 4;
    let mut start = end - rump;
    match rump {
        0 | 1 => (),
        2 => sort2(&mut s[start ..], cmpleftright),
        3 => sort3(&mut s[start ..], cmpleftright),
        _ => unreachable!(),
    }

    // We iterate backwards through the slice in blocks of size = 4:
    //
    //           A                         B                         C
    //    |             |           |             |           |---size *2---|
    //    |      |-size-|           |-size-|      |           |      |      |
    //  xxy0xx xxy1xx xxx0xx      xxy0xx xxy1xx xxx0xx      xxy0xx xxy1xx xxx0xx
    //         start   end        start   end                start   mid    end
    //
    // When start & 4 == 1 (A), then we just sort the right block of 4.
    // When start & 4 == 0 (B), then the right block of 4 was sorted on the previous iteration,
    // and we sort the left block of 4.  Now that we have two sorted blocks, we merge the block
    // of 8 (C).  We then check if start & 8 == 0 (y).  If it is, then we have two sorted
    // blocks of 8 that can be merged into a block of 16.  We continue to do this until we
    // reach a size where (start & (power of two) == 1), indicating that we are sorting the
    // right-hand block of a pair.  This method of merging provides good cache locality, and
    // is cache-oblivious.
    //
    // while start & size == 0 {
    //     let mid = end;
    //     end = mid + size;
    //     merge_inplace(&mut s[start .. end], size, cmpleftright, cmprightleft, recurse);
    //     size *= 2;
    // }
    //
    // Of course, we need to deal with trailing blocks that are not power of two, and also with
    // `start == 0`, where there is no bit set to 1 to terminate the merges.  To merge the
    // final non-power-of-two block, we ensure that `end` cannot be set past the end of the
    // slice.  We also check that `mid < s.len()`.  If `mid >= s.len()`, then the next merge
    // will have nothing on the righthand side, so we are done.  When `start == 0` and the
    // righthand side has no elements, then the already sorted lefthand side is the complete
    // sorted slice.
    //
    // while start & size == 0 {
    //     let mid = end;
    //     if mid >= s.len() {break;}
    //     end = mid + size;
    //     if end > s.len() {end = s.len();}
    //     merge_inplace(&mut s[start .. end], size, cmpleftright, cmprightleft, recurse);
    //     size *= 2;
    // }
    //
    // Since `mid` is just `end` from the previous iteration, we can move the check into the
    // `while` conditional.
    //
    // while start & size == 0 && end < s.len() {
    //     end = min(end + size, s.len());
    //     merge_inplace(&mut s[start .. end], size, cmpleftright, cmprightleft, recurse);
    //     size *= 2;
    // }
    //
    while start > 0 {
        let mut end = start;
        start -= 4;
        sort4(&mut s[start .. end], cmpleftright);
        let mut size = 4usize;
        while start & size == 0 && end < s.len() {
            end = min(end + size, s.len());
            merge_inplace(&mut s[start .. end], size, cmpleftright, cmprightleft, recurse);
            size *= 2;
        }
    }
}

pub fn sort_by<T, F>(s: &mut [T], compare: &F)
where
    T: std::fmt::Debug,
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
    T: Ord + std::fmt::Debug
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
        assert_eq!(count.get(), 15); // minimum is 15
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
        super::merge_inplace(&mut s, 0, &compare, &compare, super::MAX_RECURSION_LIMIT);
        assert_eq!(count.get(), 0);
    }

    #[test]
    fn merge_0_1() {
        let mut s = [1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge_inplace(&mut s, 0, &compare, &compare, super::MAX_RECURSION_LIMIT);
        assert_eq!(count.get(), 0);
        assert_eq!(s[0], 1);
    }

    #[test]
    fn merge_1_0() {
        let mut s = [1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge_inplace(&mut s, 1, &compare, &compare, super::MAX_RECURSION_LIMIT);
        assert_eq!(count.get(), 0);
        assert_eq!(s[0], 1);
    }

    #[test]
    fn merge_1_1_ordered() {
        let mut s = [1, 2];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge_inplace(&mut s, 1, &compare, &compare, super::MAX_RECURSION_LIMIT);
        assert_eq!(count.get(), 1);
        assert_eq!(s[0], 1);
        assert_eq!(s[1], 2);
    }

    #[test]
    fn merge_1_1_unordered() {
        let mut s = [2, 1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge_inplace(&mut s, 1, &compare, &compare, super::MAX_RECURSION_LIMIT);
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
        super::merge_inplace(&mut s, 1, &compare, &compare, super::MAX_RECURSION_LIMIT);
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
        super::merge_inplace(&mut s, leftlen, &compare, &compare, super::MAX_RECURSION_LIMIT);
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
        super::merge_inplace(&mut s, leftlen, &compare, &compare, super::MAX_RECURSION_LIMIT);
        assert_eq!(count.get(), 1);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i);
        }
    }

    #[test]
    fn merge_left_alternative() {
        let mut s = [
            2, 4, 6, 8, 10, 12, 14, 16,
            1, 3, 5, 7, 9, 11, 13, 15,
        ];
        let count = Cell::new(0);
        let leftlen = s.len() / 2;
        let compare = |a: &usize, b: &usize|{count.set(count.get() + 1); usize::cmp(&a, &b)};
        super::merge_left(&mut s, leftlen, &compare, &compare);
        assert_eq!(count.get(), 26);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i + 1);
        }
    }

    #[test]
    fn merge_right_alternative() {
        let mut s = [
            2, 4, 6, 8, 10, 12, 14, 16,
            1, 3, 5, 7, 9, 11, 13, 15,
        ];
        let count = Cell::new(0);
        let leftlen = s.len() / 2;
        let compare = |a: &usize, b: &usize|{count.set(count.get() + 1); usize::cmp(&a, &b)};
        super::merge_right(&mut s, leftlen, &compare, &compare);
        assert_eq!(count.get(), 24);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i + 1);
        }
    }

    #[test]
    fn merge_recurse_alternative() {
        let mut s = [
            2, 4, 6, 8, 10, 12, 14, 16,
            1, 3, 5, 7, 9, 11, 13, 15,
        ];
        let count = Cell::new(0);
        let leftlen = s.len() / 2;
        let compare = |a: &usize, b: &usize|{count.set(count.get() + 1); usize::cmp(&a, &b)};
        super::merge_recurse(&mut s, leftlen, &compare, &compare, super::MAX_RECURSION_LIMIT);
        assert_eq!(count.get(), 26);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i + 1);
        }
    }

    #[test]
    fn merge_final_alternative() {
        let mut s = [
            2, 4, 6, 8, 10, 12, 14, 16,
            1, 3, 5, 7, 9, 11, 13, 15,
        ];
        let count = Cell::new(0);
        let leftlen = s.len() / 2;
        let compare = |a: &usize, b: &usize|{count.set(count.get() + 1); usize::cmp(&a, &b)};
        super::merge_final(&mut s, leftlen, &compare, &compare);
        assert_eq!(count.get(), 26);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i + 1);
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
        assert_eq!(profile, vec![2, 2, 3, 3, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 5, 5])
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
    fn gallop_left_0() {
        assert_eq!(super::gallop_left(&Nc(3), &[], &Nc::cmp), 0)
    }

    #[test]
    fn gallop_left_1_before() {
        assert_eq!(super::gallop_left(&Nc(1), &[Nc(2)], &Nc::cmp), 0)
    }
    #[test]
    fn gallop_left_1_after() {
        assert_eq!(super::gallop_left(&Nc(3), &[Nc(2)], &Nc::cmp), 1)
    }

    #[test]
    fn gallop_left_2_before() {
        assert_eq!(super::gallop_left(&Nc(1), &[Nc(2), Nc(4)], &Nc::cmp), 0)
    }
    #[test]
    fn gallop_left_2_middle() {
        assert_eq!(super::gallop_left(&Nc(3), &[Nc(2), Nc(4)], &Nc::cmp), 1)
    }
    #[test]
    fn gallop_left_2_after() {
        assert_eq!(super::gallop_left(&Nc(5), &[Nc(2), Nc(4)], &Nc::cmp), 2)
    }

    #[test]
    fn gallop_left_3_before() {
        assert_eq!(super::gallop_left(&Nc(1), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp), 0)
    }
    #[test]
    fn gallop_left_3_lt() {
        // Default to Ordering::Less if the value should be inserted before equal values
        let compare = |a: &Nc, b: &Nc|{Nc::cmp(&a, &b).then(Ordering::Less)};
        assert_eq!(super::gallop_left(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &compare), 1)
    }
    #[test]
    fn gallop_left_3_le() {
        // Default to Ordering::Greater if value should be inserted after equal values
        let compare = |a: &Nc, b: &Nc|{Nc::cmp(&a, &b).then(Ordering::Greater)};
        assert_eq!(super::gallop_left(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &compare), 2)
    }
    #[test]
    fn gallop_left_3_after() {
        assert_eq!(super::gallop_left(&Nc(7), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp), 3)
    }

    #[test]
    fn gallop_left_2powm1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::gallop_left(&v, &s, &|&a, &b|{count.set(count.get() + 1); usize::cmp(&a, &b).then(Ordering::Less)}), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 3, 3, 2, 2])
    }

    #[test]
    fn gallop_left_2pow() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::gallop_left(&v, &s, &|&a, &b|{count.set(count.get() + 1); usize::cmp(&a, &b).then(Ordering::Less)}), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![7, 7, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 3, 3, 2, 2])
    }

    #[test]
    fn gallop_left_2powp1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::gallop_left(&v, &s, &|&a, &b|{count.set(count.get() + 1); usize::cmp(&a, &b).then(Ordering::Less)}), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 5, 5, 5, 5, 3, 3, 2, 2])
    }

    #[test]
    fn gallop_left_20() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::gallop_left(&v, &s, &|&a, &b|{count.set(count.get() + 1); usize::cmp(&a, &b).then(Ordering::Less)}), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![7, 7, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 5, 5, 5, 5, 3, 3, 2, 2])
    }

    #[test]
    fn binary_search_0() {
        assert_eq!(super::binary_search(&Nc(3), &[], 0, &Nc::cmp), 0)
    }

    #[test]
    fn binary_search_1_before() {
        assert_eq!(super::binary_search(&Nc(1), &[Nc(2)], 0, &Nc::cmp), 0)
    }
    #[test]
    fn binary_search_1_after() {
        assert_eq!(super::binary_search(&Nc(3), &[Nc(2)], 0, &Nc::cmp), 1)
    }

    #[test]
    fn binary_search_2_before() {
        assert_eq!(super::binary_search(&Nc(1), &[Nc(2), Nc(4)], 0, &Nc::cmp), 0)
    }
    #[test]
    fn binary_search_2_middle() {
        assert_eq!(super::binary_search(&Nc(3), &[Nc(2), Nc(4)], 0, &Nc::cmp), 1)
    }
    #[test]
    fn binary_search_2_after() {
        assert_eq!(super::binary_search(&Nc(5), &[Nc(2), Nc(4)], 0, &Nc::cmp), 2)
    }

    #[test]
    fn binary_search_3_before() {
        assert_eq!(super::binary_search(&Nc(1), &[Nc(2), Nc(4), Nc(6)], 0, &Nc::cmp), 0)
    }
    #[test]
    fn binary_search_3_lt() {
        // Default to Ordering::Less if the value should be inserted before equal values
        let compare = |a: &Nc, b: &Nc|{Nc::cmp(&a, &b).then(Ordering::Less)};
        assert_eq!(super::binary_search(&Nc(4), &[Nc(2), Nc(4), Nc(6)], 0, &compare), 1)
    }
    #[test]
    fn binary_search_3_le() {
        // Default to Ordering::Greater if value should be inserted after equal values
        let compare = |a: &Nc, b: &Nc|{Nc::cmp(&a, &b).then(Ordering::Greater)};
        assert_eq!(super::binary_search(&Nc(4), &[Nc(2), Nc(4), Nc(6)], 0, &compare), 2)
    }
    #[test]
    fn binary_search_3_after() {
        assert_eq!(super::binary_search(&Nc(7), &[Nc(2), Nc(4), Nc(6)], 0, &Nc::cmp), 3)
    }

    #[test]
    fn binary_search_2powm1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::binary_search(&v, &s, 0, &|&a, &b|{count.set(count.get() + 1); usize::cmp(&a, &b).then(Ordering::Less)}), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4])
    }

    #[test]
    fn binary_search_stable() {
        let s = [1, 5, 5, 5, 5, 5, 8];
        let count = Cell::new(0);
        super::binary_search(&5, &s, 0, &|&a, &b|{count.set(count.get() + 1); i32::cmp(&a, &b).then(Ordering::Less)});
        assert_eq!(count.get(), 3);
    }

    #[test]
    fn binary_search_unstable() {
        // If compare can return Equal, then insertion point returned on first match
        // Since first comparsion finds matching value, it will return immediately.
        let s = [1, 5, 5, 5, 5, 5, 8];
        let count = Cell::new(0);
        super::binary_search(&5, &s, 0, &|&a, &b|{count.set(count.get() + 1); i32::cmp(&a, &b)});
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
    #[should_panic]
    fn swap_ends_zero() {
        let mut buf = [1, 2, 3, 4, 5, 6];
        super::swap_ends(&mut buf, 0);
        assert_eq!(buf, [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    #[should_panic]
    fn rotate0_0() {
        let mut buf: [i32; 0] = [];
        super::rotate(&mut buf, 0);
        assert_eq!(buf, []);
    }

    #[test]
    #[should_panic]
    fn rotate0_1() {
        let mut buf = [4];
        super::rotate(&mut buf, 0);
        assert_eq!(buf, [4]);
    }

    #[test]
    #[should_panic]
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

        fn sort_stable(vec: Vec<u8>) -> bool {
            let mut vec = vec.clone();
            let mut s: Vec<(usize, u8)>= vec.drain(..).enumerate().collect();
            super::sort_by(&mut s, &|a: &(usize, u8), b: &(usize, u8)| a.1.cmp(&b.1));
            s.windows(2).all(|v| v[0].1 < v[1].1 || (v[0].1 == v[1].1 && v[0].0 < v[1].0))
        }
    }

    // Check that the benchmarks sort correctly
    extern crate rand;
    use self::rand::{thread_rng, Rng};

    fn gen_ascending(len: usize) -> Vec<u64> {
        (0..len as u64).collect()
    }

    fn gen_descending(len: usize) -> Vec<u64> {
        (0..len as u64).rev().collect()
    }

    fn gen_random(len: usize) -> Vec<u64> {
        let mut rng = thread_rng();
        rng.gen_iter::<u64>().take(len).collect()
    }

    fn gen_mostly_ascending(len: usize) -> Vec<u64> {
        let mut rng = thread_rng();
        let mut v = gen_ascending(len);
        for _ in (0usize..).take_while(|x| x * x <= len) {
            let x = rng.gen::<usize>() % len;
            let y = rng.gen::<usize>() % len;
            v.swap(x, y);
        }
        v
    }

    fn gen_mostly_descending(len: usize) -> Vec<u64> {
        let mut rng = thread_rng();
        let mut v = gen_descending(len);
        for _ in (0usize..).take_while(|x| x * x <= len) {
            let x = rng.gen::<usize>() % len;
            let y = rng.gen::<usize>() % len;
            v.swap(x, y);
        }
        v
    }

    fn gen_short_runs(len: usize) -> Vec<u64> {
        // swap odds and evens to create many short runs
        // 7 2 1 4 3 6 5 0
        let mut v = gen_ascending(len);
        let last = v.len() - 1;
        v.swap(0, last);
        for i in 1 .. last {
            if i % 2 == 0 {
                v.swap(i - 1, i);
            }
        }
        v
    }

    fn gen_nightmare(_: usize) -> Vec<u64> {
        let mut left = Vec::<u64>::new();
        let mut right = Vec::<u64>::new();
        let mut val = 0;
        for i in 2 .. 513 {
            right.push(val);
            val += 1;
            for _ in 0 .. i {
                left.push(val);
                val += 1;
            }
        }
        left.append(&mut right);
        left
    }

    fn gen_marenight(_: usize) -> Vec<u64> {
        let mut left = Vec::<u64>::new();
        let mut right = Vec::<u64>::new();
        let mut val = 0;
        for i in 2 .. 513 {
            right.push(val);
            val += 1;
            for _ in 0 .. i {
                left.push(val);
                val += 1;
            }
        }
        right.append(&mut left);
        right
    }

    fn gen_big_random(len: usize) -> Vec<[u64; 16]> {
        let mut rng = thread_rng();
        rng.gen_iter().map(|x| [x; 16]).take(len).collect()
    }

    fn gen_big_ascending(len: usize) -> Vec<[u64; 16]> {
        (0..len as u64).map(|x| [x; 16]).take(len).collect()
    }

    fn gen_big_descending(len: usize) -> Vec<[u64; 16]> {
        (0..len as u64).rev().map(|x| [x; 16]).take(len).collect()
    }

    macro_rules! bench_test {
        ($name:ident, $gen:expr, $len:expr) => {
            #[test]
            fn $name() {
                let mut s = $gen($len);
                super::sort(&mut s);
                assert!(s.windows(2).all(|v| v[0] <= v[1]));
            }
        }
    }

    bench_test!(small_random_bench_test, gen_random, 10);
    bench_test!(small_ascending_bench_test, gen_ascending, 10);
    bench_test!(small_descending_bench_test, gen_descending, 10);

    bench_test!(small_big_random_bench_test, gen_big_random, 10);
    bench_test!(small_big_ascending_bench_test, gen_big_ascending, 10);
    bench_test!(small_big_descending_bench_test, gen_big_descending, 10);

    bench_test!(medium_random_bench_test, gen_random, 100);
    bench_test!(medium_ascending_bench_test, gen_ascending, 100);
    bench_test!(medium_descending_bench_test, gen_descending, 100);

    bench_test!(large_short_runs_bench_test, gen_short_runs, 10000);
    bench_test!(large_random_bench_test, gen_random, 10000);
    bench_test!(large_ascending_bench_test, gen_ascending, 10000);
    bench_test!(large_descending_bench_test, gen_descending, 10000);
    bench_test!(large_mostly_ascending_bench_test, gen_mostly_ascending, 10000);
    bench_test!(large_mostly_descending_bench_test, gen_mostly_descending, 10000);

    bench_test!(nightmare_bench_test, gen_nightmare, 1);
    bench_test!(marenight_bench_test, gen_marenight, 1);

    bench_test!(large_big_random_bench_test, gen_big_random, 10000);
    bench_test!(large_big_ascending_bench_test, gen_big_ascending, 10000);
    bench_test!(large_big_descending_bench_test, gen_big_descending, 10000);

}
