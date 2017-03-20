extern crate gcd;

use std::cmp::min;
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


fn insertion_point<T, F>(
    value: &T, buffer: &[T], compare: &F, when_equal: Ordering, initial: usize, offset: usize
) -> usize
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
    // a range containing the position.  For example, with initial = 0 and offset = 1, the searched
    // positions are: 0, 1, 3, 7, 15, 31,...
    //
    // If the position is more likely to be later in the sequence, the other values can be used.
    // With initial = 1, offset = 2 the code tests positions: 1, 3, 7, 15, ... using one less
    // comparison for most values, at the cost of one additional comparison for position 0.
    //
    // The offset value must be a power of two and the initial value must be one less than a power
    // of two, to ensure that the next stage gets a balanced binary tree.
    //
    // Setting initial == length will skip the gallop and go straight to binary search.
    // Setting offset == length will test the initial value and then go to binary search.
    debug_assert!(initial >= length || (initial + 1).is_power_of_two());
    debug_assert!(offset >= length || offset.is_power_of_two());
    let mut p2 = offset;
    while p2 - offset + initial < length {
        let trial = p2 - offset + initial;
        let mut leg = compare(value, &buffer[trial]);
        if leg == Ordering::Equal {
            leg = when_equal;
        };
        match leg {
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
    while hi > lo {
        let trial = lo + (hi - lo) / 2;
        debug_assert!(trial < length);
        let mut leg = compare(value, &buffer[trial]);
        if leg == Ordering::Equal {
            leg = when_equal;
        };
        match leg {
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
    debug_assert!(k > 1 && k < slen - 1);
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
        // So this seems to be the best we can do right now:
        let mut tmp: [u64; STACK_OBJECT_SIZE / 8] = std::mem::uninitialized();
        let t = tmp.as_mut_ptr() as *mut T;
        let src = s.as_ptr();
        let dst = s.as_mut_ptr();
        std::ptr::copy_nonoverlapping(src, t, llen);
        std::ptr::copy(src.offset(llen as isize), dst, rlen);
        std::ptr::copy_nonoverlapping(t, dst.offset(rlen as isize), llen);
        std::mem::forget(tmp);
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
        std::mem::forget(tmp);
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

fn merge<T, F>(s: &mut [T], split: usize, compare: &F, leftright: Ordering, rightleft: Ordering)
    where
        F: Fn(&T, &T) -> Ordering
{
    // The slice to be sorted is divided into S0 | L | M | R | S1
    // The indexes into the slice are l0, m0, r0, r1
    let mut l0 = 0;
    let mut m0 = split;
    let mut r0 = split;
    let mut r1 = s.len();

    macro_rules! llen {() => (m0 - l0)}
    macro_rules! mlen {() => (r0 - m0)}
    macro_rules! rlen {() => (r1 - r0)}

    if llen!() == 0 || rlen!() == 0 {
        return;
    }

    // R may contain values that are higher than l_max.  These values are already in their final
    // position, so we can move them from R to S1.
    let pos = insertion_point(&s[m0 - 1], &s[r0 .. r1], compare, leftright, 0, r1);
    if pos == 0 {
        // l_max < r_0 -> L-R is already sorted
        //
        // Although this code is shrinking the size of the sequence and setting up a useful
        // invariant, it also provides a third behaviour which is useful when this function is
        // called as part of a mergesort. By passing (initial, offset) = (0, length) it uses the
        // first comparison to check the value against the first point of the sequence.
        //
        // This means already ordered sequences are merged with one comparison, and an entire
        // mergesort of already ordered data will take the minimum possible (n-1) comparisons.
        // This is useful because much real data is close to already sorted, so optimising this
        // case is valuable.
        //
        // Since mergesort typically passes buffers of size 2^n, this means the binary search occurs
        // over the remaining 2^n-1 values (i.e. is completely balanced).  Hence, this initial test
        // has no effect on the worst case of log2 n.
        return;
    }
    r1 = r0 + pos;
    // l_max is largest value

    // L may contain values that are lower than r_0.  These values are already in their final
    // position, so we can move them from L to S0.  Note, we ignore l_max since we know it is
    // larger than r_0.  This is why we don't need to test whether |L| = 0.
    let pos = insertion_point(&s[r0], &s[l0 .. m0 - 1], compare, rightleft, 0, 1);
    l0 += pos;
    // r0 is smallest value

    if llen!() == 1 || rlen!() == 1 {
        // since r_0 is smallest value, if |R| = 1, we just need to swap L and R
        // since l_max is largest value, if |L| = 1, we just need to swap L and R
        rotate(&mut s[l0 .. r1], rlen!());
        return;
    }

    // At this point, we have several invariants:
    debug_assert!(compare(&s[l0], &s[r0]) != Ordering::Less);           // 1. r_0 is min value
    debug_assert!(compare(&s[r1 - 1], &s[m0 - 1]) != Ordering::Greater);// 2. l_max is max value
    debug_assert!(llen!() > 1);                                         // 3. |L| > 1
    debug_assert!(mlen!() == 0);                                        // 4. |M| == 0
    debug_assert!(rlen!() > 1);                                         // 5. |R| > 1

    // find X in R where X[i] < L[0]
    // - Since R[0] is minimum, L[0] > R[0], so exclude R[0] from search
    let mut xlen = insertion_point(&s[l0], &s[r0 + 1 .. r1], compare, leftright, 0, 1) + 1;
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
        let zlen = insertion_point(&s[r0 + xlen], &s[l0 + 1 .. m0 - 1], compare, rightleft, 0, 1) + 1;
        if llen!() < xlen + zlen {
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
            xlen = insertion_point(&s[l0], &s[r0 + 1 .. r1], compare, leftright, 0, 1) + 1;
        }
        else {
            // Method E2
            debug_assert!(xlen + zlen <= llen!());
            // swap L[X] with X
            swap_ends(&mut s[l0 + zlen .. r0 + xlen], xlen);
            // rotate Z - X to X - Z
            rotate(&mut s[l0 .. l0 + zlen + xlen], xlen);
            l0 += xlen + zlen;
            r0 += xlen;
            if rlen!() == 1 {
                // since r_0 is smallest value, if |R| = 1, rotate L-M-R to R-M-L
                rotate(&mut s[m0 .. r1], rlen!());
                rotate(&mut s[l0 .. r1], mlen!() + rlen!());
                return;
            }
            // assert |M| > 0 and R[0] is minimum
            debug_assert!(mlen!() > 0); // |M| > 0
            // find X in R where X[i] < M[0]
            debug_assert!(r0 + 1 < r1);
            xlen = insertion_point(&s[m0], &s[r0 + 1 .. r1], compare, leftright, 0, 1) + 1;
            loop {
                if llen!() < xlen {
                    // |L| < |X|:
                    // rotate(L, M)
                    rotate(&mut s[l0 .. r0], mlen!());
                    // merge M-L to L, and X still valid
                    m0 = r0;
                    break
                }
                if xlen == rlen!() {
                    // |X| == |R|:
                    // Method B2
                    // rotate M - R to R - M
                    rotate(&mut s[m0 .. r1], rlen!());
                    // rotate L - R - M to R - M - L
                    rotate(&mut s[l0 .. r1], mlen!() + rlen!());
                    // merge completed
                    return
                }
                // find Y in M where Y[i] < R'[0]
                let ylen = insertion_point(&s[r0 + xlen], &s[m0 + 1 .. r0], compare, rightleft, 0, 1) + 1;
                if ylen == mlen!() {
                    // |Y| == |M|:
                    // find Z in L where Z[i] < R'[0]
                    let zlen = insertion_point(&s[r0 + xlen], &s[l0 .. m0 - 1], compare, rightleft, 0, 1);
                    // Methods C1 and C3 both start with a rotate of Y - X
                    rotate(&mut s[m0 .. r0 + xlen], xlen);
                    if llen!() < xlen + ylen + zlen {
                        // Method C1
                        // rotate Y - X to X - Y
                        // rotate Z - LX - LY - L' - X - Y to X - Y - Z - LX - LY - L'
                        rotate(&mut s[l0 .. r0 + xlen], xlen + ylen);
                        l0 += xlen + ylen + zlen;
                        r0 += xlen;
                        m0 = r0;
                        if llen!() == 1 || rlen!() == 1 {
                            // since r_0 is smallest value, if |R| = 1, we just need to swap L and R
                            // since l_max is largest value, if |L| = 1, we just need to swap L and R
                            rotate(&mut s[l0 .. r1], rlen!());
                            return;
                        }
                        // find X in R where X[i] < L[0]
                        debug_assert!(r0 + 1 < r1);
                        xlen = insertion_point(&s[l0], &s[r0 + 1 .. r1], compare, leftright, 0, 1) + 1;
                        break
                    }
                    // Method C3
                    debug_assert!(xlen + ylen <= llen!());
                    // rotate Y - X to X - Y
                    // rotate Z - LX - LY to LX - LY - Z
                    rotate(&mut s[l0 .. l0 + zlen + xlen + ylen], xlen + ylen);
                    // swap LX - LY with X - Y
                    swap_ends(&mut s[l0 .. r0 + xlen], xlen + ylen);
                    l0 += xlen + ylen + zlen;
                    r0 += xlen;
                } else {
                    if llen!() < mlen!() + xlen {
                        // this method works for |L| < |X| + |Y|. However, |M| is a major
                        // factor in the amount of work done, so we use it instead of |Y|.
                        // Since |Y| < |M|, we always take the work that A1 can't handle.
                        // Method A2
                        debug_assert!(xlen <= llen!());
                        // swap LX with X
                        swap_ends(&mut s[l0 .. r0 + xlen], xlen);
                        // rotate LY - L' - Y to Y - LY - L'
                        rotate(&mut s[l0 + xlen .. m0 + ylen], ylen);
                        l0 += xlen + ylen;
                        m0 += ylen;
                        r0 += xlen;
                    } else {
                        // Method A1
                        debug_assert!(xlen + ylen <= llen!());
                        // rotate Y - M' - X to M' - X - Y
                        rotate(&mut s[m0 .. r0 + xlen], mlen!() - ylen + xlen);
                        // swap LX - LY with X - Y
                        swap_ends(&mut s[l0 .. r0 + xlen], xlen + ylen);
                        l0 += xlen + ylen;
                        r0 += xlen;
                    }
                }
                debug_assert!(mlen!() > 0); // |M| > 0
                if rlen!() == 1 {
                    // since r_0 is smallest value, if |R| = 1, rotate L-M-R to R-M-L
                    rotate(&mut s[m0 .. r1], rlen!());
                    rotate(&mut s[l0 .. r1], mlen!() + rlen!());
                    return;
                }
                debug_assert!(r0 + 1 < r1);
                xlen = insertion_point(&s[m0], &s[r0 + 1 .. r1], compare, leftright, 0, 1) + 1;
            }
        }
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
                rotate(&mut chunk[0 .. 3], 1);
            } else {
                chunk.swap(1, 2);
            }
        }
        if compare(&chunk[1], &chunk[3]) == Ordering::Greater {
            if compare(&chunk[0], &chunk[3]) == Ordering::Greater {
                rotate(chunk, 1);
            } else {
                rotate(&mut chunk[1 .. 4], 1);
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
                    rotate(&mut s[length4 .. length4 + 3], 1);
                } else {
                    s.swap(length4 + 1, length4 + 2);
                }
            }
        }
    }
}

pub fn sort_by<T, F>(s: &mut [T], compare: &F)
    where
        F: Fn(&T, &T) -> Ordering
{
    let length = s.len();
    sort4(s, compare);
    let mut blk = 4;  // size of blocks already sorted
    while blk < length {
        let mut start = 0;
        let mut pivot = blk;
        let mut end = 2 * blk;
        while pivot < length {
            merge(
                &mut s[start .. min(end, length)],
                blk,
                compare,
                Ordering::Less,
                Ordering::Greater
            );
            start = end;
            pivot = start + blk;
            end = pivot + blk;
        }
        blk *= 2;
    }
}

pub fn sort<T>(s: &mut [T])
    where T: Ord
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
        super::merge(
            &mut s, 0, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, Ordering::Greater
        );
        assert_eq!(count.get(), 0);
    }

    #[test]
    fn merge_0_1() {
        let mut s = [1];
        let count = Cell::new(0);
        super::merge(
            &mut s, 0, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, Ordering::Greater
        );
        assert_eq!(count.get(), 0);
        assert_eq!(s[0], 1);
    }

    #[test]
    fn merge_1_0() {
        let mut s = [1];
        let count = Cell::new(0);
        super::merge(
            &mut s, 1, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, Ordering::Greater
        );
        assert_eq!(count.get(), 0);
        assert_eq!(s[0], 1);
    }

    #[test]
    fn merge_1_1_ordered() {
        let mut s = [1, 2];
        let count = Cell::new(0);
        super::merge(
            &mut s, 1, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, Ordering::Greater
        );
        assert_eq!(count.get(), 1);
        assert_eq!(s[0], 1);
        assert_eq!(s[1], 2);
    }

    #[test]
    fn merge_1_1_unordered() {
        let mut s = [2, 1];
        let count = Cell::new(0);
        super::merge(
            &mut s, 1, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, Ordering::Greater
        );
        assert_eq!(count.get(), 1);
        assert_eq!(s[0], 1);
        assert_eq!(s[1], 2);
    }

    #[test]
    fn merge_1_n() {
        let mut s = [7, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10];
        let count = Cell::new(0);
        super::merge(
            &mut s, 1, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, Ordering::Greater
        );
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
        super::merge(
            &mut s, leftlen, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, Ordering::Greater
        );
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
        super::merge(
            &mut s, leftlen, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, Ordering::Greater
        );
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
        super::merge(&mut s, leftlen, &Nc::cmp, Ordering::Less, Ordering::Greater);
        for (i, elem) in s.iter().enumerate() {
            assert_eq!(*elem, Nc(i as i32));
        }
    }

    #[test]
    fn bisect_0() {
        assert_eq!(super::insertion_point(&Nc(3), &[], &Nc::cmp, Ordering::Less, 0, 1), 0)
    }

    #[test]
    fn bisect_1_before() {
        assert_eq!(super::insertion_point(&Nc(1), &[Nc(2)], &Nc::cmp, Ordering::Less, 0, 1), 0)
    }
    #[test]
    fn bisect_1_after() {
        assert_eq!(super::insertion_point(&Nc(3), &[Nc(2)], &Nc::cmp, Ordering::Less, 0, 1), 1)
    }

    #[test]
    fn bisect_2_before() {
        assert_eq!(super::insertion_point(&Nc(1), &[Nc(2), Nc(4)], &Nc::cmp, Ordering::Less, 0, 1), 0)
    }
    #[test]
    fn bisect_2_middle() {
        assert_eq!(super::insertion_point(&Nc(3), &[Nc(2), Nc(4)], &Nc::cmp, Ordering::Less, 0, 1), 1)
    }
    #[test]
    fn bisect_2_after() {
        assert_eq!(super::insertion_point(&Nc(5), &[Nc(2), Nc(4)], &Nc::cmp, Ordering::Less, 0, 1), 2)
    }

    #[test]
    fn bisect_3_before() {
        assert_eq!(super::insertion_point(&Nc(1), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp, Ordering::Less, 0, 1), 0)
    }
    #[test]
    fn bisect_3_lt() {
        // Use less-than if the value should be inserted before equal values
        assert_eq!(super::insertion_point(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp, Ordering::Less, 0, 1), 1)
    }
    #[test]
    fn bisect_3_le() {
        // Use less-than-or-equal if value should be inserted after equal values
        assert_eq!(super::insertion_point(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp, Ordering::Greater, 0, 1), 2)
    }
    #[test]
    fn bisect_3_after() {
        assert_eq!(super::insertion_point(&Nc(7), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp, Ordering::Less, 0, 1), 3)
    }

    #[test]
    fn bisect_2powm1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::insertion_point(&v, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, s.len(), 1), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4])
    }

    #[test]
    fn bisect_2pow() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::insertion_point(&v, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, 0, s.len()), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![1, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5])
    }

    #[test]
    fn bisect_2powp1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::insertion_point(&v, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, 0, 1), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![1, 2, 4, 4, 6, 6, 6, 6, 8, 8, 8, 8, 8, 8, 8, 8, 6, 6])
    }

    #[test]
    fn bisect_20_0_1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::insertion_point(&v, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, 0, 1), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![1, 2, 4, 4, 6, 6, 6, 6, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 7, 7])
    }

    #[test]
    fn bisect_20_1_2() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::insertion_point(&v, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less, 1, 2), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![2, 2, 3, 3, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6])
    }

    #[test]
    fn bisect_unstable() {
        // If Ordering::Equal passed, then insertion point returned on first match
        // Here we pass the length as the initial value, so first test will be in middle.
        // Since that matches the value, it will return immediately.
        let s = [1, 5, 5, 5, 5, 5, 8];
        let count = Cell::new(0);
        super::insertion_point(&5, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Equal, s.len(), 1);
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
