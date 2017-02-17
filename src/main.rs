extern crate gcd;

use gcd::Gcd;


fn split_biased(n: usize) -> usize {
    // Return a split point that ensures that the RHS is a balanced binary tree.  A balanced binary
    // tree contains 2^k - 1 nodes. Hence the length can be represented in binary by all-ones on
    // the right (e.g. 15 = 00001111).  Masking off the leftmost 1 of this value gives 7 (00000111)
    // a.k.a. 2^(k-1) - 1.
    //
    // Testing the value at position 7 tells us whether the next test should be on the 7 values
    // below 7 (0-6) or the 7 values above 7 (8-14). This is the ideal binary search requiring
    // log2 n tests for any search.
    //
    // Initially, we may get a sequence which has between 2^(k-1) and 2^k - 2 nodes, i.e. an
    // unbalanced binary tree.  In this case, some of the branches may require fewer tests than
    // others.  Since we are comparing the starts of sorted sequences, we would like to bias the
    // selection of shorter branches to use fewer tests on the left side.
    //
    // This is done by ensuring the right side of the test still returns 2^(k-1) - 1 nodes and the
    // left side gets the smaller sequence to test.  Conveniently, this is also achieved by masking
    // off the highest 1 bit.  This technique gives us somewhat of an equivalent to galloping in
    // other sorting algorithms.
    //
    // For example, a sequence of 21 elements has length 00010101.  Masking off the high 1 bit
    // gives 00000101 = 5. If we test the value at position 5, the next test will either be 6-20
    // (15 values, a balanced binary tree requiring 4 more tests) or 0-4 (5 values). Removing the
    // leftmost bit of 6 (00000101) gives 1.  Testing 1 wi1l make the next test 2-4 (3 values, a
    // balanced binary tree requiring 2 more tests) or 0, requiring 1 additional test.  Hence, the
    // rightmost values require 5 tests, the leftmost value requires 3 tests, and other low values
    // require 4 tests.

    let mask = (1 as usize).rotate_right(n.leading_zeros() + 1);
    n & !mask
}

fn insertion_point<T, F>(value: &T, buffer: &[T], before: &mut F) -> (usize, usize)
    where
        F: FnMut(&T, &T) -> bool
{
    // Find the insertion point where the value would fit
    // All elements to the left of the insertion point are "before" the value
    // and the value is "before" all elements to the right of the insertion point.
    // The "before" function returns true if it's first argument is "before" the second.
    // Typically, this will be PartialOrd::lt to insert the value before equal values
    // or PartialOrd::le to insert the value after other equal values.
    let length = buffer.len();
    let mut lo = 0;   // lowest candidate
    let mut hi = length; // highest candidate
    while hi > lo {
        let trial = split_biased(hi - lo) + lo;
        debug_assert!(trial < length);
        if before(&buffer[trial], value) {
            lo = trial + 1
        } else {
            hi = trial
        }
    }
    debug_assert!(lo == hi);
    (lo, length)
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
        let (pos, length) = insertion_point(&s[r0], &s[l0 .. l1], &mut le);
        if pos == length {
            // r0 > lmax - done
            return
        } else {
            // swap values, and add l_pos into M
            let l_pos = l0 + pos;
            s.swap(l_pos, r0);
            l0 = l_pos + 1;
            r0 += 1;
        }
        while l0 < l1 && l1 < r0 && r0 < r1 {
            // While L, M, and R exist, find insertion point of M[0] in R
            let (pos, length) = insertion_point(&s[l1], &s[r0 .. r1], &mut lt);
            if pos == length {
                // R < M < L
                // LMR -> RML
                // first, swap min(|L|,|R|) to make:
                // Ra | Lb | Ma La | Rb, one of Lb or Rb is empty
                // then, if Lb is empty, rotate Ma-La-Rb to Rb-Ma-La, return
                // else rotate Lb-Ma-La to Ma-La-Lb, return
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
                    rotate(&mut s[l0 .. r1], llen - rlen);
                }
                return
            } else {
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
        let (pos, length) = insertion_point(&s[l0], &s[r0 .. r1], &mut lt);
        if pos == length {
            rotate(&mut s[l0 .. r1], r1 - r0);
        } else if pos != 0 {
            rotate(&mut s[l0 .. r0 + pos], pos);
        }
        // else already in position
    } else if r1 - r0 == 1 {
        // |R| = 1: Just insert it into L
        let (pos, length) = insertion_point(&s[r0], &s[l0 .. l1], &mut le);
        if pos < length {
            rotate(&mut s[l0 + pos .. r1], 1);
        }
        // else already in position
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
    fn split_biased_0() {
        assert_eq!(super::split_biased(0), 0);
    }

    #[test]
    fn split_biased_1() {
        assert_eq!(super::split_biased(1), 0);
    }

    #[test]
    fn split_biased_2() {
        assert_eq!(super::split_biased(2), 0);
    }

    #[test]
    fn split_biased_3() {
        assert_eq!(super::split_biased(3), 1);
    }

    #[test]
    fn split_biased_2powm1() {
        assert_eq!(super::split_biased(31), 15);
    }

    #[test]
    fn split_biased_2pow() {
        assert_eq!(super::split_biased(32), 0);
    }

    #[test]
    fn split_biased_2powp1() {
        assert_eq!(super::split_biased(33), 1);
    }

    #[test]
    fn split_biased_10101() {
        assert_eq!(super::split_biased(21), 5)
    }

    // A non-copy but comparable type is useful for testing, as bad moves are hidden by Copy types.
    #[derive(PartialEq,Eq,PartialOrd,Ord)]
    struct Nc(i32);

    #[test]
    fn bisect0() {
        assert_eq!(super::insertion_point(&Nc(3), &[], &mut Nc::lt), (0, 0))
    }

    #[test]
    fn bisect1_before() {
        assert_eq!(super::insertion_point(&Nc(1), &[Nc(2)], &mut Nc::lt), (0, 1))
    }
    #[test]
    fn bisect1_after() {
        assert_eq!(super::insertion_point(&Nc(3), &[Nc(2)], &mut Nc::lt), (1, 1))
    }

    #[test]
    fn bisect2_before() {
        assert_eq!(super::insertion_point(&Nc(1), &[Nc(2), Nc(4)], &mut Nc::lt), (0, 2))
    }
    #[test]
    fn bisect2_middle() {
        assert_eq!(super::insertion_point(&Nc(3), &[Nc(2), Nc(4)], &mut Nc::lt), (1, 2))
    }
    #[test]
    fn bisect2_after() {
        assert_eq!(super::insertion_point(&Nc(5), &[Nc(2), Nc(4)], &mut Nc::lt), (2, 2))
    }

    #[test]
    fn bisect3_before() {
        assert_eq!(super::insertion_point(&Nc(1), &[Nc(2), Nc(4), Nc(6)], &mut Nc::lt), (0, 3))
    }
    #[test]
    fn bisect3_lt() {
        // Use less-than if the value should be inserted before equal values
        assert_eq!(super::insertion_point(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &mut Nc::lt), (1, 3))
    }
    #[test]
    fn bisect3_le() {
        // Use less-than-or-equal if value should be inserted after equal values
        assert_eq!(super::insertion_point(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &mut Nc::le), (2, 3))
    }
    #[test]
    fn bisect3_after() {
        assert_eq!(super::insertion_point(&Nc(7), &[Nc(2), Nc(4), Nc(6)], &mut Nc::lt), (3, 3))
    }

    #[test]
    fn bisect3_2powm1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let slen = s.len();
        let mut profile = Vec::new();
        for v in 0 .. slen + 1 {
            let mut count = 0;
            {
                assert_eq!(
                    super::insertion_point(&v, &s, &mut |&a, &b|{count += 1; a < b}),
                    (v, slen)
                );
            }
            profile.push(count);
        }
        assert_eq!(profile, vec![4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4])
    }

    #[test]
    fn bisect3_2pow() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let slen = s.len();
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let mut count = 0;
            {
                assert_eq!(
                    super::insertion_point(&v, &s, &mut |&a, &b|{count += 1; a < b}),
                    (v, slen)
                );
            }
            profile.push(count);
        }
        assert_eq!(profile, vec![1, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5])
    }

    #[test]
    fn bisect3_2powp1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let slen = s.len();
        let mut profile = Vec::new();
        for v in 0 .. slen + 1 {
            let mut count = 0;
            {
                assert_eq!(
                    super::insertion_point(&v, &s, &mut |&a, &b|{count += 1; a < b}),
                    (v, slen)
                );
            }
            profile.push(count);
        }
        assert_eq!(profile, vec![2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5])
    }

    #[test]
    fn bisect3_20() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];
        let slen = s.len();
        let mut profile = Vec::new();
        for v in 0 .. slen + 1 {
            let mut count = 0;
            {
                assert_eq!(
                    super::insertion_point(&v, &s, &mut |&a, &b|{count += 1; a < b}),
                    (v, slen)
                );
            }
            profile.push(count);
        }
        assert_eq!(profile, vec![2, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5])
    }

    #[test]
    fn bisect3_21() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];
        let slen = s.len();
        let mut profile = Vec::new();
        for v in 0 .. slen + 1 {
            let mut count = 0;
            {
                assert_eq!(
                    super::insertion_point(&v, &s, &mut |&a, &b|{count += 1; a < b}),
                    (v, slen)
                );
            }
            profile.push(count);
        }
        assert_eq!(profile, vec![3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5])
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