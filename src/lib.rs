#![feature(stmt_expr_attributes)]

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

// Tuning parameters:

// The maximum GCD for which reverse is used to rotate. Above this value, block swapping is used.
const ROTATE_REVERSE_MAX: usize = 4;

fn gallop_from_left<T, F>(value: &T, buffer: &[T], compare: &F) -> usize
where
    F: Fn(&T, &T) -> Ordering,
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
    let mut lo = 0; // lowest candidate
    let mut hi = length; // highest candidate

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
            }
            Ordering::Greater => {
                lo = trial + 1;
                interval *= 2;
            }
            Ordering::Equal => {
                return trial;
            }
        }
    }

    // At this point, either hi == length, and we're processing the rump of the sequence, or
    // lo-hi contains 2^n - 1 elements containing the correct position.  2^n - 1 elements gives us
    // a balanced binary tree.  Perform binary search to find the final insertion position.
    debug_assert!(hi == length || (hi - lo + 1).is_power_of_two());
    binary_search(value, &buffer[..hi], lo, compare)
}

fn binary_search<T, F>(value: &T, buffer: &[T], start: usize, compare: &F) -> usize
where
    F: Fn(&T, &T) -> Ordering,
{
    let length = buffer.len();
    let mut lo = start; // lowest candidate
    let mut hi = length; // highest candidate
    while hi > lo {
        let trial = lo + (hi - lo) / 2;
        debug_assert!(trial < length);
        match unsafe { compare(value, &buffer.get_unchecked(trial)) } {
            Ordering::Less => {
                hi = trial;
            }
            Ordering::Greater => {
                lo = trial + 1;
            }
            Ordering::Equal => {
                return trial;
            }
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
    T: std::ops::Add<Output = T> + std::ops::Sub<Output = T> + Copy + PartialOrd,
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
    } else {
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
        s[..k].reverse();
        s[k..].reverse();
    } else {
        // Otherwise, we move each block up by k positions, using the first block as working space.
        let mut j = k;
        for _ in 0..slen / blksize - 1 {
            swap_ends(&mut s[0..j + blksize], blksize);
            j = add_modulo(j, k, slen);
        }
        debug_assert!(j == 0);
    }
}

fn rotate<T>(s: &mut [T], rlen: usize) {
    // Rotate the last rlen elements to the front of the slice.
    // given a slice of 0..n, move n-rlen..n to front and 0..n-rlen to end
    debug_assert!(rlen > 0);
    let llen = s.len() - rlen;
    debug_assert!(llen > 0);
    if llen == rlen {
        swap_ends(s, llen);
    } else {
        rotate_gcd(s, rlen);
    }
}

fn rotate_left<T>(s: &mut [T], llen: usize) {
    // Rotate the llen elements to the back of the slice.
    debug_assert!(llen > 0);
    if llen == 1 {
        rotate_left_1(s);
        return;
    }
    let rlen = s.len() - llen;
    if rlen == 1 {
        rotate_right_1(s);
        return;
    }
    debug_assert!(rlen > 0);
    if llen == rlen {
        swap_ends(s, llen);
    } else {
        rotate_gcd(s, rlen);
    }
}

fn rotate_left_1<T>(s: &mut [T]) {
    debug_assert!(s.len() > 1);
    let r = s.len() - 1;
    unsafe {
        let src = s.as_ptr();
        let dst = s.as_mut_ptr();
        let tmp = std::ptr::read(src);
        std::ptr::copy(src.add(1), dst, r);
        std::ptr::write(dst.add(r), tmp);
    }
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

#[inline]
fn merge<T, F, G>(b: &mut [T], i: usize, cmpleftright: &F, cmprightleft: &G) -> usize
where
    T: std::fmt::Debug,
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering,
{
    debug_assert!(i > 0 && i < b.len());
    if cmpleftright(unsafe { b.get_unchecked(i - 1) }, unsafe {
        b.get_unchecked(i)
    }) == Ordering::Less
    {
        return i;
    }
    merge1(b, i, cmpleftright, cmprightleft)
}

fn merge1<T, F, G>(b: &mut [T], mut i: usize, cmpleftright: &F, cmprightleft: &G) -> usize
where
    T: std::fmt::Debug,
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering,
{
    // println!("merge {:?} {:?}", &b[..i], &b[i..]);
    let mut g = 0;
    loop {
        // println!("mergeloop {:?} {:?} {:?}", &b[..g], &b[g..i], &b[i..]);
        if i - g == 1 {
            let d = gallop_from_left(
                unsafe { b.get_unchecked(g) },
                unsafe { b.get_unchecked(i + 1..) },
                cmpleftright,
            ) + i
                + 1;
            rotate_left_1(unsafe {b.get_unchecked_mut(g..d)});
            // println!("merged1 {:?}", &b);
            return d;
        }
        g += gallop_from_left(
            unsafe { b.get_unchecked(i) },
            unsafe { b.get_unchecked(g..i - 1) },
            cmprightleft,
        );
        let mut d = i + 1;
        loop {
            // println!("childloop {:?} {:?} {:?} {:?}", &b[..g], &b[g..i], &b[i..d], &b[d..]);
            d += gallop_from_left(
                unsafe { b.get_unchecked(g) },
                unsafe { b.get_unchecked(d..) },
                cmpleftright,
            );
            if d == b.len() {
                rotate_left(unsafe { b.get_unchecked_mut(g..) }, i - g);
                // println!("merged {:?}", b);
                return d;
            }
            // println!("before {:?} {:?} {:?} {:?}", &b[..g], &b[g..i], &b[i..d], &b[d..]);
            if d - i + 1 >= i - g {
                rotate_left(unsafe { b.get_unchecked_mut(g..d) }, i - g);
                g += d - i + 1;
                i = d;
                if cmpleftright(unsafe { b.get_unchecked(i - 1) }, unsafe {
                    b.get_unchecked(i)
                }) == Ordering::Less
                {
                    return i;
                }
                // println!("after1 {:?} {:?} {:?} {:?}", &b[..g], &b[g..i], &b[i..d], &b[d..]);
                break;
            } else {
                // d - i >= 1 -> d - i + 1 >= 2; i - g > d - i + 1 -> i - g > 2
                let buf = b.as_mut_ptr();
                unsafe {
                    let tmp = buf.offset(g as isize).read();
                    for j in i..d {
                        std::ptr::write(buf.offset(g as isize), buf.offset(j as isize).read());
                        // std::ptr::copy_nonoverlapping(buf.offset(j as isize), buf.offset(g as isize), 1);
                        g += 1;
                        std::ptr::write(buf.offset(j as isize), buf.offset(g as isize).read());
                        // std::ptr::copy_nonoverlapping(buf.offset(g as isize), buf.offset(j as isize), 1);
                    }
                    std::ptr::write(buf.offset(g as isize), tmp);
                }
                g += 1;
                // println!("after {:?} {:?} {:?} {:?}", &b[..g], &b[g..i], &b[i..d], &b[d..]);
                if d < b.len() {
                    d = merge(
                        unsafe { b.get_unchecked_mut(i..) },
                        d - i,
                        cmpleftright,
                        cmprightleft,
                    ) + i;
                }
            }
        }
    }
}

macro_rules! ascending {
    ( $comparison:expr ) => {
        $comparison != Ordering::Greater
    };
}

fn sort4<T, F>(s: &mut [T], compare: &F) -> bool
where
    T: std::fmt::Debug,
    F: Fn(&T, &T) -> Ordering,
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
            if !ascending!(compare(&s[2], &s[3])) {
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
            if !ascending!(compare(&s[0], &s[2])) {
                //
                s.swap(0, 2);
            }
            // 1324(1324) 1423(1423) 1432(1432) 1324(2314)
            // 1423(2413) 2431(2431) 1432(3412) 2431(3421)
            if ascending!(compare(&s[2], &s[3])) {
                // 1324(1324) 1423(1423) 1324(2314) 1423(2413)
                if !ascending!(compare(&s[1], &s[3])) {
                    s.swap(1, 3);
                }
                // 1324(1324) 1324(1423) 1324(2314) 1324(2413)
                s.swap(1, 2);
                debug!("sort4 {:?}", s);
                false
            } else {
                // 1432(1432) 2431(2431) 1432(3412) 2431(3421)
                if !ascending!(compare(&s[0], &s[3])) {
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
        if !ascending!(compare(&s[1], &s[2])) {
            // 3214 4213 4312 4321
            if ascending!(compare(&s[2], &s[3])) {
                // 3214 4213 4312
                s.swap(0, 2);
                // 1234(3214) 1243(4213) 1342(4312)
                if !ascending!(compare(&s[2], &s[3])) {
                    // 1243(4213) 1342(4312)
                    s.swap(2, 3);
                    // 1234(4213) 1324(4312)
                    if !ascending!(compare(&s[1], &s[2])) {
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
            if !ascending!(compare(&s[0], &s[2])) {
                s.swap(0, 2);
            }
            // 2134(2134) 2143(2143) 2134(3124) 3142(3142)
            // 3241(3241) 2143(4123) 3142(4132) 3241(4231)
            if ascending!(compare(&s[0], &s[3])) {
                // 2134(2134) 2143(2143) 2134(3124) 2143(4123)
                if !ascending!(compare(&s[2], &s[3])) {
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
    F: Fn(&T, &T) -> Ordering,
{
    // Handcrafted sort for chunks of 3
    assert!(s.len() == 3);
    if !ascending!(compare(&s[0], &s[1])) {
        s.swap(0, 1);
    }
    if !ascending!(compare(&s[1], &s[2])) {
        if ascending!(compare(&s[0], &s[2])) {
            s.swap(1, 2);
        } else {
            rotate_right_1(&mut s[..3]);
        }
    }
}

fn sort2<T, F>(s: &mut [T], compare: &F)
where
    F: Fn(&T, &T) -> Ordering,
{
    // Handcrafted sort for chunks of 2
    assert!(s.len() == 2);
    if !ascending!(compare(&s[0], &s[1])) {
        s.swap(0, 1);
    }
}

fn sort_by_ordering<T, F, G>(s: &mut [T], cmpleftright: &F, cmprightleft: &G)
where
    T: std::fmt::Debug,
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&T, &T) -> Ordering,
{
    let end = s.len();
    let rump = end % 4;
    let mut start = end - rump;
    match rump {
        0 | 1 => (),
        2 => sort2(&mut s[start..], cmpleftright),
        3 => sort3(&mut s[start..], cmpleftright),
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
        sort4(&mut s[start..end], cmpleftright);
        let mut size = 4usize;
        while start & size == 0 && end < s.len() {
            end = min(end + size, s.len());
            merge(&mut s[start..end], size, cmpleftright, cmprightleft);
            size *= 2;
        }
    }
}

pub fn sort_by<T, F>(s: &mut [T], compare: &F)
where
    T: std::fmt::Debug,
    F: Fn(&T, &T) -> Ordering,
{
    sort_by_ordering(
        s,
        &|ref a, ref b| compare(&a, &b).then(Ordering::Less),
        &|ref a, ref b| compare(&a, &b).then(Ordering::Greater),
    )
}

pub fn sort<T>(s: &mut [T])
where
    T: Ord + std::fmt::Debug,
{
    sort_by(s, &T::cmp);
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::cmp::Ordering;

    // A non-copy but comparable type is useful for testing, as bad moves are hidden by Copy types.
    #[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
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
        super::sort_by(&mut s, &|a: &usize, b: &usize| {
            count.set(count.get() + 1);
            a.cmp(&b)
        });
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
    fn merge_1_1_ordered() {
        let mut s = [1, 2];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32| {
            count.set(count.get() + 1);
            i32::cmp(&a, &b)
        };
        super::merge(&mut s, 1, &compare, &compare);
        assert_eq!(count.get(), 1);
        assert_eq!(s[0], 1);
        assert_eq!(s[1], 2);
    }

    #[test]
    fn merge_1_1_unordered() {
        let mut s = [2, 1];
        let count = Cell::new(0);
        let compare = |a: &i32, b: &i32| {
            count.set(count.get() + 1);
            i32::cmp(&a, &b)
        };
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
        let compare = |a: &usize, b: &usize| {
            count.set(count.get() + 1);
            usize::cmp(&a, &b)
        };
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
        let compare = |a: &usize, b: &usize| {
            count.set(count.get() + 1);
            usize::cmp(&a, &b)
        };
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
        let compare = |a: &usize, b: &usize| {
            count.set(count.get() + 1);
            usize::cmp(&a, &b)
        };
        super::merge(&mut s, leftlen, &compare, &compare);
        assert_eq!(count.get(), 1);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i);
        }
    }

    #[test]
    fn merge_alternative() {
        let mut s = [2, 4, 6, 8, 10, 12, 14, 16, 1, 3, 5, 7, 9, 11, 13, 15];
        let count = Cell::new(0);
        let leftlen = s.len() / 2;
        let compare = |a: &usize, b: &usize| {
            count.set(count.get() + 1);
            usize::cmp(&a, &b)
        };
        super::merge(&mut s, leftlen, &compare, &compare);
        assert_eq!(count.get(), 22);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, i + 1);
        }
    }

    #[test]
    fn gallop_from_left_0() {
        assert_eq!(super::gallop_from_left(&Nc(3), &[], &Nc::cmp), 0)
    }

    #[test]
    fn gallop_from_left_1_before() {
        assert_eq!(super::gallop_from_left(&Nc(1), &[Nc(2)], &Nc::cmp), 0)
    }
    #[test]
    fn gallop_from_left_1_after() {
        assert_eq!(super::gallop_from_left(&Nc(3), &[Nc(2)], &Nc::cmp), 1)
    }

    #[test]
    fn gallop_from_left_2_before() {
        assert_eq!(
            super::gallop_from_left(&Nc(1), &[Nc(2), Nc(4)], &Nc::cmp),
            0
        )
    }
    #[test]
    fn gallop_from_left_2_middle() {
        assert_eq!(
            super::gallop_from_left(&Nc(3), &[Nc(2), Nc(4)], &Nc::cmp),
            1
        )
    }
    #[test]
    fn gallop_from_left_2_after() {
        assert_eq!(
            super::gallop_from_left(&Nc(5), &[Nc(2), Nc(4)], &Nc::cmp),
            2
        )
    }

    #[test]
    fn gallop_from_left_3_before() {
        assert_eq!(
            super::gallop_from_left(&Nc(1), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp),
            0
        )
    }
    #[test]
    fn gallop_from_left_3_lt() {
        // Default to Ordering::Less if the value should be inserted before equal values
        let compare = |a: &Nc, b: &Nc| Nc::cmp(&a, &b).then(Ordering::Less);
        assert_eq!(
            super::gallop_from_left(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &compare),
            1
        )
    }
    #[test]
    fn gallop_from_left_3_le() {
        // Default to Ordering::Greater if value should be inserted after equal values
        let compare = |a: &Nc, b: &Nc| Nc::cmp(&a, &b).then(Ordering::Greater);
        assert_eq!(
            super::gallop_from_left(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &compare),
            2
        )
    }
    #[test]
    fn gallop_from_left_3_after() {
        assert_eq!(
            super::gallop_from_left(&Nc(7), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp),
            3
        )
    }

    #[test]
    fn gallop_from_left_2powm1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let mut profile = Vec::new();
        for v in 0..s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(
                super::gallop_from_left(&v, &s, &|&a, &b| {
                    count.set(count.get() + 1);
                    usize::cmp(&a, &b).then(Ordering::Less)
                }),
                v
            );
            profile.push(count.get());
        }
        assert_eq!(
            profile,
            vec![2, 2, 3, 3, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6]
        )
    }

    #[test]
    fn gallop_from_left_2pow() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let mut profile = Vec::new();
        for v in 0..s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(
                super::gallop_from_left(&v, &s, &|&a, &b| {
                    count.set(count.get() + 1);
                    usize::cmp(&a, &b).then(Ordering::Less)
                }),
                v
            );
            profile.push(count.get());
        }
        assert_eq!(
            profile,
            vec![2, 2, 3, 3, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 4]
        )
    }

    #[test]
    fn gallop_from_left_2powp1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let mut profile = Vec::new();
        for v in 0..s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(
                super::gallop_from_left(&v, &s, &|&a, &b| {
                    count.set(count.get() + 1);
                    usize::cmp(&a, &b).then(Ordering::Less)
                }),
                v
            );
            profile.push(count.get());
        }
        assert_eq!(
            profile,
            vec![2, 2, 3, 3, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 5, 5]
        )
    }

    #[test]
    fn gallop_from_left_20() {
        let s = [
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        ];
        let mut profile = Vec::new();
        for v in 0..s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(
                super::gallop_from_left(&v, &s, &|&a, &b| {
                    count.set(count.get() + 1);
                    usize::cmp(&a, &b).then(Ordering::Less)
                }),
                v
            );
            profile.push(count.get());
        }
        assert_eq!(
            profile,
            vec![2, 2, 3, 3, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6]
        )
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
        assert_eq!(
            super::binary_search(&Nc(1), &[Nc(2), Nc(4)], 0, &Nc::cmp),
            0
        )
    }
    #[test]
    fn binary_search_2_middle() {
        assert_eq!(
            super::binary_search(&Nc(3), &[Nc(2), Nc(4)], 0, &Nc::cmp),
            1
        )
    }
    #[test]
    fn binary_search_2_after() {
        assert_eq!(
            super::binary_search(&Nc(5), &[Nc(2), Nc(4)], 0, &Nc::cmp),
            2
        )
    }

    #[test]
    fn binary_search_3_before() {
        assert_eq!(
            super::binary_search(&Nc(1), &[Nc(2), Nc(4), Nc(6)], 0, &Nc::cmp),
            0
        )
    }
    #[test]
    fn binary_search_3_lt() {
        // Default to Ordering::Less if the value should be inserted before equal values
        let compare = |a: &Nc, b: &Nc| Nc::cmp(&a, &b).then(Ordering::Less);
        assert_eq!(
            super::binary_search(&Nc(4), &[Nc(2), Nc(4), Nc(6)], 0, &compare),
            1
        )
    }
    #[test]
    fn binary_search_3_le() {
        // Default to Ordering::Greater if value should be inserted after equal values
        let compare = |a: &Nc, b: &Nc| Nc::cmp(&a, &b).then(Ordering::Greater);
        assert_eq!(
            super::binary_search(&Nc(4), &[Nc(2), Nc(4), Nc(6)], 0, &compare),
            2
        )
    }
    #[test]
    fn binary_search_3_after() {
        assert_eq!(
            super::binary_search(&Nc(7), &[Nc(2), Nc(4), Nc(6)], 0, &Nc::cmp),
            3
        )
    }

    #[test]
    fn binary_search_2powm1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let mut profile = Vec::new();
        for v in 0..s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(
                super::binary_search(&v, &s, 0, &|&a, &b| {
                    count.set(count.get() + 1);
                    usize::cmp(&a, &b).then(Ordering::Less)
                }),
                v
            );
            profile.push(count.get());
        }
        assert_eq!(
            profile,
            vec![4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]
        )
    }

    #[test]
    fn binary_search_stable() {
        let s = [1, 5, 5, 5, 5, 5, 8];
        let count = Cell::new(0);
        super::binary_search(&5, &s, 0, &|&a, &b| {
            count.set(count.get() + 1);
            i32::cmp(&a, &b).then(Ordering::Less)
        });
        assert_eq!(count.get(), 3);
    }

    #[test]
    fn binary_search_unstable() {
        // If compare can return Equal, then insertion point returned on first match
        // Since first comparsion finds matching value, it will return immediately.
        let s = [1, 5, 5, 5, 5, 5, 8];
        let count = Cell::new(0);
        super::binary_search(&5, &s, 0, &|&a, &b| {
            count.set(count.get() + 1);
            i32::cmp(&a, &b)
        });
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
        let mut buf = [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
        ];
        super::rotate(&mut buf, 6);
        assert_eq!(
            buf,
            [16, 17, 18, 19, 20, 21, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        );
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
            let mut s: Vec<(usize, u8)>= vec.into_iter().enumerate().collect();
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
        rng.gen_iter::<u64>().map(|x| x % 256).take(len).collect()
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
        for i in 1..last {
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
        for i in 2..513 {
            right.push(val);
            val += 1;
            for _ in 0..i {
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
        for i in 2..513 {
            right.push(val);
            val += 1;
            for _ in 0..i {
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
                assert!(s.windows(2).all(|v| v[0] <= v[1]), "{:?}", s);
            }
        };
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
    bench_test!(
        large_mostly_ascending_bench_test,
        gen_mostly_ascending,
        10000
    );
    bench_test!(
        large_mostly_descending_bench_test,
        gen_mostly_descending,
        10000
    );

    bench_test!(nightmare_bench_test, gen_nightmare, 1);
    bench_test!(marenight_bench_test, gen_marenight, 1);

    bench_test!(large_big_random_bench_test, gen_big_random, 10000);
    bench_test!(large_big_ascending_bench_test, gen_big_ascending, 10000);
    bench_test!(large_big_descending_bench_test, gen_big_descending, 10000);
}
