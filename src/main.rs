extern crate gcd;

use gcd::Gcd;


fn insertion_point<T, F>(value: &T, buffer: &[T], before: &mut F) -> Option<usize>
    where
        F: FnMut(&T, &T) -> bool
{
    // Find the insertion point where the value would fit
    // All elements to the left of the insertion point are "before" the value
    // and the value is "before" all elements to the right of the insertion point.
    // The "before" function returns true if it's first argument is "before" the second.
    // Typically, this will be PartialOrd::lt to insert the value before equal values
    // or PartialOrd::le to insert the value after other equal values.
    // The function performs a binary search, but is biased to look for values before or after
    // all the values in the slice.  It starts with the mid-point. Depending on that test, it
    // then tests whether the value is before slice, or value is after slice. It then bisects
    // the half identified by the first two comparisons.
    // Returns index to first element in the slice that is not before the value. If there is no
    // element, it returns None (rather than slice length). This ensures that the caller
    // special-cases that event, to avoid using an element that is not in the slice.
    // TODO - could support a RANDOM flag that uses normal binary search instead of biased
    // to allow user to flag whether data is truly random
    if buffer.is_empty() {
        return None
    }
    let mut lo = 0;   // lowest candidate
    let mut hi = buffer.len() - 1; // highest candidate
    let trial = hi / 2;
    if before(&buffer[trial], value) {
        if trial == hi || before(&buffer[hi], value) {
            return None
        }
        lo = trial + 1;
    } else {
        if trial == lo || !before(&buffer[lo], value) {
            return Some(lo)
        }
        lo = lo + 1;
        hi = trial;
    }
    while hi > lo {
        let trial = (hi - lo) / 2 + lo;  // (hi+lo)/2 is more prone to overflow (however unlikely)
        if before(&buffer[trial], value) {
            lo = trial + 1
        } else {
            hi = trial
        }
    }
    debug_assert!(lo == hi);
    return Some(lo)
}

fn swap_sequence<T>(s: &mut [T], a: usize, b: usize, k: usize) {
    for i in 0..k {
        s.swap(a + i, b + i)
    }
}

fn rotate<T>(s: &mut [T], k: usize) {
    // Rotate the last k elements to the front of the slice.
    // given a slice of 0..n, move n-k..n to front and 0..n-k to end
    // for i = 0..k, add size of second section: new position = (i + k) % n
    // for i = k..n, subtract size of first section: new position = (i - n + k) % n = (i + k) % n
    // so all elements need to have the same move applied
    // There are gcd(k, n-k) cycles
    // TODO - possibly there is a speed-up by running the for loop inside the while. This will
    // access data more linearly, which may improve CPU caching
    // TODO - we can use unchecked gets to possibly improve performance, since indexes are
    // constrained by modulo
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    assert!(n > k);
    let c = k.gcd(n - k);
    for i in 0 .. c {
        let mut j = (i + k) % n;
        while j != i {
            s.swap(i, j);
            j = (j + k) % n;
        }
    }
}

fn merge<T, F>(mut s: &mut [T], split: usize, mut lt: F, mut le: F)
    where
        T: Ord,
        F: FnMut(&T, &T) -> bool
{
    // The slice to be sorted is divided into S0 | L | M | R | S1
    // The indexes into the slice are l0, l1, r0, r1
    let mut l0 = 0;
    let mut l1 = split;
    let mut r0 = split;
    let mut r1 = s.len();
    while l1 - l0 > 1 && r1 - r0 > 1 {
        assert!(l1 == r0);  // M is empty
        // Find r0 in L
        match insertion_point(&s[r0], &s[l0 .. l1], &mut le) {
            None => {
                // r0 > lmax - done
                return
            }
            Some(pos) => {
                // swap values, and add r0 into M
                let ins = l0 + pos;
                s.swap(ins, r0);
                l0 = ins + 1;
                r0 += 1;
            }
        }
        while l0 < l1 && l1 < r0 && r0 < r1 {
            // While L, M, and R exist, find insertion point of M[0] in R
            match insertion_point(&s[l1], &s[r0 .. r1], &mut lt) {
                None => {
                    // R < M < L
                    // LMR -> RML
                    // first, swap min(|L|,|R|) to make:
                    // S(from Ra)-Lb-Ma-Mb(from La)-Rb, one of Lb or Rb is empty
                    // then, if Lb is empty, rotate Ma-Mb-Rb to Rb-Ma-Mb, return
                    // else rotate Lb-Ma-Mb to Ma-Mb-Lb, return
                    let llen = l1 - l0;
                    let rlen = r1 - r0;
                    // TODO - remove if with:
                    // let maxlen = max(llen, rlen);
                    // let minlen = min(llen, rlen);
                    // swap_sequence(&mut s, l0, r0, minlen);
                    // l0 += minlen;
                    // r0 += minlen;
                    // rotate(&mut s[l0 .. r1], maxlen - minlen);
                    if llen < rlen {
                        swap_sequence(&mut s, l0, r0, llen);
                        l0 += llen;
                        // r0 += llen;
                        rotate(&mut s[l0 .. r1], rlen - llen);
                    } else {
                        swap_sequence(&mut s, l0, r0, rlen);
                        l0 += rlen;
                        // r0 += rlen;
                        rotate(&mut s[l0 .. r1], llen - rlen)
                    }
                    return
                }
                Some(pos) => {
                    // L-M-R0..pos-Rpos..
                    //swap L/R to min |L|, pos
                    // R0-L1-M-L0-R0x-R1, either L1 is empty or R0x is empty
                    // if L1 is empty, rotate M-L0-R0x to R0x-M-L0, R0-R0x-M[0] => S, M->L
                    // else R0-L1-M-L0-R1
                    let llen = l1 - l0;
                    if llen < pos {
                        swap_sequence(&mut s, l0, r0, llen);
                        // L is empty
                        rotate(&mut s[l1 .. r0 + pos], pos - llen);
                        l0 += pos + 1; // Ra + M0
                        l1 = r0 + pos;
                        r0 = l1;
                    } else {
                        swap_sequence(&mut s, l0, r0, pos);
                        // find where R0 goes in M-L0. If None, then rotate L1-M-L0 -> M-L0-L1
                        // else rotate L1 and M < R0. Then swap R0 and L1,0.
                        // or insertion sort R0 into M
                    }
                }
            }
            // match insertion_point(&s[r0], &s[l1 .. r0], le) {
            //     None => {
            //         // all of M goes before R
            //         // if |L| < |M|, rotate L-M, no more M
            //         // else
            //         // swap L-M, keep M
            //     }
            //     Some(pos) => {
            //         // L0-L1-M0-M1-R
            //         // if |L| < |M0|, rotate L-M0 to M0-L, no more M
            //         // else swap L0/M0, keep M, assert R[0] < M[0]
            //     }
            // }
        }
        // if M exists, but L doesn't, L=M
    }
    if l1 - l0 == 1 {
        // |L| = 1: Just insert it into R
        match insertion_point(&s[l0], &s[r0 .. r1], &mut lt) {
            None => rotate(&mut s[l0 .. r1], r1 - r0),
            Some(pos) if pos != 0 => rotate(&mut s[l0 .. r0 + pos], pos),
            _ => {
                // already in position
            },
        }
    } else if r1 - r0 == 1 {
        // |R| = 1: Just insert it into L
        match insertion_point(&s[r0], &s[l0 .. l1], &mut le) {
            None => {
                // already in position
            }
            Some(pos) => rotate(&mut s[l0 + pos .. r1], 1),
        }
    } // at least one of |L| and |R| == 0
}

#[cfg(not(test))]
fn main() {
    let mut a = vec![2, 4, 6, 1, 3, 5];
    merge(&mut a, 3, &mut i32::lt, &mut i32::le)
}

#[cfg(test)]
mod tests {
    #[test]
    fn bisect0() {
        assert_eq!(super::insertion_point(&3, &[], &mut i32::lt), None)
    }

    #[test]
    fn bisect1_before() {
        assert_eq!(super::insertion_point(&1, &[2], &mut i32::lt), Some(0))
    }
    #[test]
    fn bisect1_after() {
        assert_eq!(super::insertion_point(&3, &[2], &mut i32::lt), None)
    }

    #[test]
    fn bisect2_before() {
        assert_eq!(super::insertion_point(&1, &[2, 4], &mut i32::lt), Some(0))
    }
    #[test]
    fn bisect2_middle() {
        assert_eq!(super::insertion_point(&3, &[2, 4], &mut i32::lt), Some(1))
    }
    #[test]
    fn bisect2_after() {
        assert_eq!(super::insertion_point(&5, &[2, 4], &mut i32::lt), None)
    }

    #[test]
    fn bisect3_before() {
        assert_eq!(super::insertion_point(&1, &[2, 4, 6], &mut i32::lt), Some(0))
    }
    #[test]
    fn bisect3_lt() {
        // Use less-than if the value should be inserted before equal values
        assert_eq!(super::insertion_point(&4, &[2, 4, 6], &mut i32::lt), Some(1))
    }
    #[test]
    fn bisect3_le() {
        // Use less-than-or-equal if value should be inserted after equal values
        assert_eq!(super::insertion_point(&4, &[2, 4, 6], &mut i32::le), Some(2))
    }
    #[test]
    fn bisect3_after() {
        assert_eq!(super::insertion_point(&7, &[2, 4, 6], &mut i32::lt), None)
    }

    #[test]
    fn bisect3_even() {
        let s = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let mut profile = Vec::new();
        for v in 1 .. 18 {
            let mut count = 0;
            {
                super::insertion_point(&v, &s, &mut |&a, &b|{count += 1; a < b});
            }
            profile.push(count);
        }
        assert_eq!(profile, vec![2, 5, 5, 5, 5, 5, 5, 4, 5, 5, 5, 5, 5, 5, 5, 5, 2])
    }

    #[test]
    fn bisect3_odd() {
        let s = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let mut profile = Vec::new();
        for v in 1 .. 17 {
            let mut count = 0;
            {
                super::insertion_point(&v, &s, &mut |&a, &b|{count += 1; a < b});
            }
            profile.push(count);
        }
        assert_eq!(profile, vec![2, 5, 5, 5, 5, 5, 5, 4, 5, 5, 5, 5, 5, 5, 4, 2])
    }

    #[test]
    fn swap_sequence_adjacent() {
        let mut buf = [1, 2, 3, 4, 5, 6];
        super::swap_sequence(&mut buf, 0, 3, 3);
        assert_eq!(buf, [4, 5, 6, 1, 2, 3]);
    }

    #[test]
    fn swap_sequence_disjoint() {
        let mut buf = [1, 2, 3, 4, 5, 6];
        super::swap_sequence(&mut buf, 1, 4, 2);
        assert_eq!(buf, [1, 5, 6, 4, 2, 3]);
    }

    #[test]
    fn swap_sequence_zero() {
        let mut buf = [1, 2, 3, 4, 5, 6];
        super::swap_sequence(&mut buf, 0, 3, 0);
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

}