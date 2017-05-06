extern crate gcd;

use std::cmp::Ordering;

use gcd::Gcd;

#[cfg(test)]
#[macro_use]
extern crate quickcheck;


// Tuning parameters:

// The algorithm may use this many bytes on the stack as a buffer.  Only one buffer of this size
// exists on the stack at any time.
const STACK_OBJECT_SIZE: usize = 2048;

// The maximum GCD for which reverse is used to rotate. Above this value, block swapping is used.
const ROTATE_REVERSE_MAX: usize = 4;

// The minimum shift used in the insertion merge algorithm. Use low factors, to increase the GCD
// and make rotation faster.
const INSERTION_MERGE_MIN_SHIFT: usize = 2 * 2 * 3 * 5;


fn gallop_right<T, F>(value: &T, buffer: &[T], compare: &F) -> usize
where
    F: Fn(&T, &T) -> Ordering
{
    // Find the insertion point in an ordered buffer where the value should be inserted to maintain
    // the ordering.  All elements to the left of the insertion point are Less than the value and
    // the value is Less than all elements to the right of the insertion point.  The ordering is
    // defined by the "compare" function.  If the "compare" function returns Equal, then the
    // behaviour is defined by the when_equal parameter. If Less or Greater, the compare acts as
    // though the when_equal value was returned by compare(value, &buffer[i]). This is useful for
    // enforcing stability.  If the when_equal value is Equal, then the caller doesn't care about
    // stability and the function returns immediately with one (of possibly many) valid insertion
    // points.
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
                return trial;
            }
        }
    }

    // At this point, either hi == length, and we're processing the rump of the sequence, or
    // lo-hi is a balanced binary tree containing the correct position.  A balanced binary tree
    // contains 2^n - 1 elements.  Perform binary search to find the final insertion position.
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
    for i in 0..k {
        unsafe {
            let pa: *mut T = s.get_unchecked_mut(i);
            let pb: *mut T = s.get_unchecked_mut(b + i);
            std::ptr::swap(pa, pb);
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
        s[0 .. k].reverse();
        s[k .. slen].reverse();
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
    // Then, a binary search of the l[max] over the remaining R is done, as any values in R that are
    // higher than l[max] are already in their final position, and can be ignored.  In a typical
    // mergesort, the two sequences will each have length 2^n, and the first step means we search one
    // less = 2^n - 1.  This is the optimal size for binary search, as it means the search must take
    // log2 n comparisons.
    //
    // Finally, we check for values in L that are less than r[0], as they are also in their final
    // position.  In this case, we gallop right, since we expect r[0] to be lower than the average
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

    // Trim off in-position low values of L to leave r[max] as smallest value
    // From above, l[max] >= r[0], so exclude l[max] from search.
    let left = gallop_right(&s[split], &s[.. split - 1], cmprightleft);

    Some((left, right))
}

fn insertion_merge<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G)
where
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    if let Some((left, right)) = trim(s, split, cmpleftright, cmprightleft) {
        insertion_merge_trimmed(&mut s[left .. right], split - left, cmpleftright, cmprightleft);
    }
}

fn insertion_merge_trimmed<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G)
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
    debug_assert!(cmprightleft(&s[right - 1], &s[split - 1]) != Ordering::Greater);
    // 4. r_0 is min value
    debug_assert!(cmpleftright(&s[left], &s[split]) != Ordering::Less);

    let mut idx = 1;
    while llen!() > 1 {
        idx = gallop_right(&s[left], &s[split + idx .. right], cmpleftright) + idx;
        // R[.. idx] < L[0] < R[idx ..]
        // R[idx] = first R element with non-zero insertion point in L
        if idx == rlen!() {
            // all of R is less than L
            break
        }
        if idx > llen!() {
            rotate(&mut s[left .. split + idx - 1], idx - 1);
            left += idx - 1;
            split += idx - 1;
            idx = 1;
        }
        // we know R[idx] > L[0], so exclude it
        let pos = gallop_right(&s[split + idx], &s[left + 1 .. split - 1], cmprightleft) + 1;
        // R[.. idx] < L[.. pos] < R[idx] < L[pos ..] ? R[idx + 1 ..]
        if pos < idx {
            // move lowest values in R to leftmost position in L
            // L[idx - 1] < L[idx]
            swap_ends(&mut s[left .. split + idx], idx);
            // L[.. idx] are smallest values.
            // R[idx - 1] < L[idx]
            left += idx;
            // R[.. pos] < R[idx] < R[pos .. idx] ? R[idx + 1 ..]
            // R[idx - 1] < L[0]
            let right = gallop_right(&s[split + idx - 1], &s[split + idx + 1 ..], cmpleftright) + idx + 1;
            // R[.. pos] < R[idx] < R[pos .. idx - 1] ? R[idx + 1 .. right] < R[idx - 1] < R[right ..]
            insertion_merge_trimmed_final(&mut s[split + pos .. split + right], idx - pos, cmpleftright, cmprightleft);
            // R[right - 1] < L[0]
            idx = right;
        } else {
            // move the highest values in L[..pos] out of the way to allow us to
            // shift the lowest values from R to front of sequence.  Do this by
            // swapping the high L values and the low R values, then rotating the
            // low L values into their final position.
            // R[.. idx] < L[.. pos - idx] < L[pos - idx .. pos] < R[idx] < L[pos ..] ? R[idx + 1 ..]
            swap_ends(&mut s[left + pos - idx .. split + idx], idx);
            // L[pos - idx .. pos] < L[.. pos - idx] < R[.. idx] < R[idx] < L[pos ..] ? R[idx + 1 ..]
            rotate(&mut s[left .. left + pos], idx);
            // L[.. pos - idx] < L[pos - idx .. pos] < R[.. idx] < R[idx] < L[pos ..] ? R[idx + 1 ..]
            // L[.. pos] now the lowest values in correct position:
            // add them to sorted by trimming L
            left += pos;
            // R[.. idx] < R[idx] < L[0 ..] ? R[idx + 1 ..]
            // the highest values moved to R are still < R[idx] and in fact
            // R[idx] is the next lowest value and is less than L[0] (was L[pos])
            idx += 1
        }
    }
    // when we get here, we know that all values in L are greater than all values in R,
    // either because |L| == 1, and we know that L[max] is greater than all values in R,
    // or we just found that L[0] is greater than all values in R
    rotate(&mut s[left .. right], rlen!());
}

fn insertion_merge_trimmed_final<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G)
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
    debug_assert!(cmprightleft(&s[right - 1], &s[split - 1]) != Ordering::Greater);
    // 4. r_0 is min value
    debug_assert!(cmpleftright(&s[left], &s[split]) != Ordering::Less);

    let mut limit = INSERTION_MERGE_MIN_SHIFT;
    if llen!() > INSERTION_MERGE_MIN_SHIFT * INSERTION_MERGE_MIN_SHIFT {
        limit = (llen!() as f64).sqrt() as usize;
    }
    let mut idx = 1;
    while llen!() > 1 {
        idx = gallop_right(&s[left], &s[split + idx .. right], cmpleftright) + idx;
        // now R[idx] = first R element with non-zero insertion point in L
        if idx == rlen!() {
            // all of R is less than L
            break
        }
        if idx > limit {
            // if idx > sqrt(|L|), shift L right
            // In theory, this can be done for any size. In practice, the cost of the multiplication
            // outweighs the benefit for small sequences, so guard this with a minimum size test.
            let n = idx - 1;
            rotate(&mut s[left .. split + idx - 1], n);
            left += n;
            split += n;
            idx = 1;
            if llen!() > INSERTION_MERGE_MIN_SHIFT * INSERTION_MERGE_MIN_SHIFT {
                limit = (llen!() as f64).sqrt() as usize;
            }
        }
        // we know R[idx] > L[0], so exclude it
        let pos = gallop_right(&s[split + idx], &s[left + 1 .. split - 1], cmprightleft) + 1;
        // now R[idx] < L[pos]
        if pos < idx {
            // move lowest values in R to leftmost position in L
            swap_ends(&mut s[left .. split + pos], pos);
            // the new R[..pos] are > R[idx - 1] but < R[idx]
            rotate(&mut s[split .. split + idx], idx - pos);
        } else {
            // move the highest values in L[..pos] out of the way to allow us to
            // shift the lowest values from R to front of sequence.  Do this by
            // swapping the high L values and the low R values, then rotating the
            // low L values into their final position.
            swap_ends(&mut s[left + pos - idx .. split + idx], idx);
            rotate(&mut s[left .. left + pos], idx);
        }
        // L[.. pos] are now the lowest values in correct position:
        // add them to sorted by trimming L
        left += pos;
        // the highest values moved to R are still < R[idx] and in fact
        // R[idx] is the next lowest value and is less than L[0] (was L[pos])
        idx += 1
    }
    // when we get here, we know that all values in L are greater than all values in R,
    // either because |L| == 1, and we know that L[max] is greater than all values in R,
    // or we just found that L[0] is greater than all values in R
    rotate(&mut s[left .. right], rlen!());
}

fn merge<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G)
where
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    if let Some((left, right)) = trim(s, split, cmpleftright, cmprightleft) {
        merge_trimmed(&mut s[left .. right], split - left, cmpleftright, cmprightleft);
    }
}

fn merge_trimmed<T, F, G>(s: &mut [T], split: usize, cmpleftright: &F, cmprightleft: &G)
where
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    // The slice to be sorted is divided into S0 | L | M | R | S1
    // The indexes into the slice are l0, m0, r0, r1
    let mut l0 = 0;
    let mut m0 = split;
    let mut r0 = split;
    let r1 = s.len();

    macro_rules! llen {() => (m0 - l0)}
    macro_rules! mlen {() => (r0 - m0)}
    macro_rules! rlen {() => (r1 - r0)}

    // 1. |L| > 0
    debug_assert!(llen!() > 0);
    // 2. |M| == 0
    debug_assert!(mlen!() == 0);
    // 3. |R| > 0
    debug_assert!(rlen!() > 0);
    // 4. l_max is max value
    debug_assert!(cmprightleft(&s[r1 - 1], &s[r0 - 1]) != Ordering::Greater);
    // 5. r_0 is min value
    debug_assert!(cmpleftright(&s[l0], &s[r0]) != Ordering::Less);

    if llen!() == 1 || rlen!() == 1 {
        // since r_0 is smallest value, if |R| = 1, we just need to swap L and R
        // since l_max is largest value, if |L| = 1, we just need to swap L and R
        rotate(&mut s[l0 .. r1], rlen!());
        return;
    }

    // find X in R where X[i] < L[0]
    // - Since R[0] is minimum, L[0] > R[0], so exclude R[0] from search
    let mut xlen = gallop_right(&s[l0], &s[r0 + 1 .. r1], cmpleftright) + 1;
    loop {
        debug_assert!(mlen!() == 0);    // |M| == 0
        if xlen == rlen!() {
            // |X| == |R|:
            // rotate(L, R)
            rotate(&mut s[l0 .. r1], rlen!());
            // merge completed
            return
        }
        // find Z in L where Z[i] < R'[0]
        // - Since L[max] > R[max], exclude L[max] from search
        // - Since R[r0 + xlen] > L[0] from previous search, exclude L[0] from search
        // - this search relies on invariant |L| > 1, tested in assert
        debug_assert!(l0 + 1 <= m0 - 1);
        let zlen = gallop_right(&s[r0 + xlen], &s[l0 + 1 .. m0 - 1], cmprightleft) + 1;
        if llen!() <= xlen + zlen {
            // |L| < 2|X| + |Z|:
            // Method E1
            // rotate Z - LX - L' - X to X - Z - LX - L'
            rotate(&mut s[l0 .. r0 + xlen], xlen);
            l0 += xlen + zlen;
            m0 += xlen;
            r0 = m0;
            if llen!() == 1 || rlen!() == 1 {
                // since r_0 is smallest value, if |R| = 1, we just need to swap L and R
                // since l_max is largest value, if |L| = 1, we just need to swap L and R
                rotate(&mut s[l0 .. r1], rlen!());
                return;
            }
            debug_assert!(r0 + 1 < r1);
            xlen = gallop_right(&s[l0], &s[r0 + 1 .. r1], cmpleftright) + 1;
        }
        else {
            // Method E2
            debug_assert!(xlen + zlen < llen!());
            // swap L[X] with X
            swap_ends(&mut s[l0 + zlen .. r0 + xlen], xlen);
            // rotate Z - X to X - Z
            rotate(&mut s[l0 .. l0 + zlen + xlen], xlen);
            l0 += xlen + zlen;
            r0 += xlen;
            // |M| > 0 and R[0] is minimum
            debug_assert!(mlen!() > 0); // |M| > 0
            debug_assert!(cmpleftright(&s[m0], &s[r0]) != Ordering::Less);
            if rlen!() == 1 {
                // since r_0 is smallest value, if |R| = 1, rotate L-M-R to R-M-L
                rotate(&mut s[m0 .. r1], rlen!());
                rotate(&mut s[l0 .. r1], mlen!() + rlen!());
                return;
            }
            // insertion merge M into R
            // Once M is in R, any M that is equal to an L will be sorted out of order.  This is
            // not a problem as long as M is selected as being <(=) R'[0], since M[max] <= L[0] but
            // M[max] == L[0] only if both == R'[0].  In a stable sort, this cannot happen, and in
            // an unstable sort, it doesn't matter if it does.
            // M[max] > R[0]
            debug_assert!(cmpleftright(&s[r0 - 1], &s[r0]) != Ordering::Less);
            // Find the first position in R > M[max]
            let pos = gallop_right(&s[r0 - 1], &s[r0 + 1 .. r1], cmpleftright) + r0 + 1;
            insertion_merge_trimmed(&mut s[m0 .. pos], mlen!(), cmpleftright, cmprightleft);
            r0 = m0;
            if llen!() == 1 || pos == r1 {
                // since l_max is largest value, if |L| = 1, rotate L-R to R-L
                // if M[max] inserted at end of R, L > R, rotate L-R to R-L
                rotate(&mut s[l0 .. r1], rlen!());
                return;
            }
            // search for the next insertion point for L[0] in R above M[max]
            xlen = gallop_right(&s[l0], &s[pos .. r1], cmpleftright) + pos - r0;
        }
    }
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

pub fn sort4<T, F>(s: &mut [T], compare: &F)
where
    F: Fn(&T, &T) -> Ordering
{
    // Handcrafted sort for chunks of 4
    let length = s.len();
    let over4 = length % 4;
    let length4 = length - over4;
    for chunk in s[0 .. length4].chunks_mut(4) {
        if compare(&chunk[0], &chunk[1]) == Ordering::Greater {
            chunk.swap(0, 1);
        }
        if compare(&chunk[1], &chunk[2]) == Ordering::Greater {
            if compare(&chunk[0], &chunk[2]) == Ordering::Greater {
                rotate_right_1(&mut chunk[0 .. 3]);
            } else {
                chunk.swap(1, 2);
            }
        }
        if compare(&chunk[1], &chunk[3]) == Ordering::Greater {
            if compare(&chunk[0], &chunk[3]) == Ordering::Greater {
                rotate_right_1(chunk);
            } else {
                rotate_right_1(&mut chunk[1 ..]);
            }
        } else if compare(&chunk[2], &chunk[3]) == Ordering::Greater {
            chunk.swap(2, 3);
        }
    }
    if over4 >= 2 {
        if compare(&s[length4], &s[length4 + 1]) == Ordering::Greater {
            s.swap(length4, length4 + 1);
        }
        if over4 == 3 {
            if compare(&s[length4 + 1], &s[length4 + 2]) == Ordering::Greater {
                if compare(&s[length4], &s[length4 + 2]) == Ordering::Greater {
                    rotate_right_1(&mut s[length4 .. length4 + 3]);
                } else {
                    s.swap(length4 + 1, length4 + 2);
                }
            }
        }
    }
}

fn sort_by_ordering<T, F, G>(s: &mut [T], cmpleftright: &F, cmprightleft: &G)
where
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering
{
    let length = s.len();
    sort4(s, cmpleftright);
    let mut blk = 4;  // size of blocks already sorted
    while blk < length {
        let mut start = 0;
        let mut end = 2 * blk;
        while end < length {
            merge(
                &mut s[start .. end],
                blk,
                cmpleftright,
                cmprightleft
            );
            start = end;
            end += 2 * blk;
        }
        // for tail, if right side contains at least one element, perform an additional merge
        if start + blk < length {
            merge(
                &mut s[start .. length],
                blk,
                cmpleftright,
                cmprightleft
            );
        }
        blk *= 2;
    }
}

pub fn sort_by<T, F>(s: &mut [T], compare: &F)
where
    F: Fn(&T, &T) -> Ordering
{
    sort_by_ordering(
        s,
        &|ref a, ref b|{compare(&a, &b).then(Ordering::Less)},
        &|ref a, ref b|{compare(&a, &b).then(Ordering::Greater)}
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
        super::merge(&mut s, 0, &compare, &compare);
        assert_eq!(count.get(), 0);
    }

    #[test]
    fn merge_0_1() {
        let mut s = [1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge(&mut s, 0, &compare, &compare);
        assert_eq!(count.get(), 0);
        assert_eq!(s[0], 1);
    }

    #[test]
    fn merge_1_0() {
        let mut s = [1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge(&mut s, 1, &compare, &compare);
        assert_eq!(count.get(), 0);
        assert_eq!(s[0], 1);
    }

    #[test]
    fn merge_1_1_ordered() {
        let mut s = [1, 2];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge(&mut s, 1, &compare, &compare);
        assert_eq!(count.get(), 1);
        assert_eq!(s[0], 1);
        assert_eq!(s[1], 2);
    }

    #[test]
    fn merge_1_1_unordered() {
        let mut s = [2, 1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::merge(&mut s, 1, &compare, &compare);
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
        super::merge(&mut s, 1, &compare, &compare);
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
        super::merge(&mut s, leftlen, &compare, &compare);
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
        super::merge(&mut s, leftlen, &compare, &compare);
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
        super::merge(&mut s, leftlen, &Nc::cmp, &Nc::cmp);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, Nc(i as i32));
        }
    }

    #[test]
    fn insertion_merge_0() {
        let mut s: [i32; 0] = [];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::insertion_merge(&mut s, 0, &compare, &compare);
        assert_eq!(count.get(), 0);
    }

    #[test]
    fn insertion_merge_0_1() {
        let mut s = [1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::insertion_merge(&mut s, 0, &compare, &compare);
        assert_eq!(count.get(), 0);
        assert_eq!(s[0], 1);
    }

    #[test]
    fn insertion_merge_1_0() {
        let mut s = [1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::insertion_merge(&mut s, 1, &compare, &compare);
        assert_eq!(count.get(), 0);
        assert_eq!(s[0], 1);
    }

    #[test]
    fn insertion_merge_1_1_ordered() {
        let mut s = [1, 2];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::insertion_merge(&mut s, 1, &compare, &compare);
        assert_eq!(count.get(), 1);
        assert_eq!(s[0], 1);
        assert_eq!(s[1], 2);
    }

    #[test]
    fn insertion_merge_1_1_unordered() {
        let mut s = [2, 1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32|{count.set(count.get() + 1); i32::cmp(&a, &b)};
        super::insertion_merge(&mut s, 1, &compare, &compare);
        // One compare required, but there are 2 debug_assert that compare
        assert!(count.get() <= 3);
        assert_eq!(s[0], 1);
        assert_eq!(s[1], 2);
    }

    #[test]
    fn insertion_merge_1_n() {
        let mut s = [7, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10];
        let count = Cell::new(0);
        let compare = |a: &usize, b: &usize|{count.set(count.get() + 1); usize::cmp(&a, &b)};
        super::insertion_merge(&mut s, 1, &compare, &compare);
        // assert_eq!(count.get(), 4);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i);
        }
    }

    #[test]
    fn insertion_merge_n_1() {
        let mut s = [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 7];
        let leftlen = s.len() - 1;
        super::insertion_merge(&mut s, leftlen, &usize::cmp, &usize::cmp);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i);
        }
    }

    #[test]
    fn insertion_merge_ordered() {
        let mut s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let count = Cell::new(0);
        let leftlen = s.len() / 2;
        let compare = |a: &usize, b: &usize|{count.set(count.get() + 1); usize::cmp(&a, &b)};
        super::insertion_merge(&mut s, leftlen, &compare, &compare);
        assert_eq!(count.get(), 1);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i);
        }
    }

    #[test]
    fn insertion_merge_alternative() {
        let mut s = [
            Nc(1), Nc(3), Nc(5), Nc(7), Nc(9), Nc(11), Nc(13), Nc(15),
            Nc(0), Nc(2), Nc(4), Nc(6), Nc(8), Nc(10), Nc(12), Nc(14),
        ];
        let leftlen = s.len() / 2;
        super::insertion_merge(&mut s, leftlen, &Nc::cmp, &Nc::cmp);
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
