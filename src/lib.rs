extern crate gcd;

use std::cmp::min;
use std::cmp::Ordering;

use gcd::Gcd;

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

#[inline]
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
    // leftmost bit of 5 (00000101) gives 1.  Testing 1 wi1l make the next test 2-4 (3 values, a
    // balanced binary tree requiring 2 more tests) or 0, requiring 1 additional test.  Hence, the
    // rightmost values require 5 tests, the leftmost value requires 3 tests, and other low values
    // require 4 tests.

    let mask = ((n >> 1) + 1).next_power_of_two();
    n & !mask
}

fn insertion_point<T, F>(value: &T, buffer: &[T], compare: &F, when_equal: Ordering) -> usize
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
    let mut lo = 0;   // lowest candidate
    let mut hi = length; // highest candidate
    while hi > lo {
        let trial = split_biased(hi - lo) + lo;
        debug_assert!(trial < length);
        match compare(value, &buffer[trial]) {
            Ordering::Less => {
                hi = trial;
            },
            Ordering::Greater => {
                lo = trial + 1;
            },
            Ordering::Equal => {
                match when_equal {
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
            },
        }
    }
    debug_assert!(lo == hi);
    lo
}

fn swap_sequence<T>(s: &mut [T], a: usize, b: usize, k: usize) {
    for i in 0..k {
        s.swap(a + i, b + i)
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
    debug_assert!(n > k);
    let c = k.gcd(n - k);
    for i in 0 .. c {
        let mut j = add_modulo(i, k, n);
        while j != i {
            s.swap(i, j);
            j = add_modulo(j, k, n);
        }
    }
}

fn merge<T, F>(s: &mut [T], split: usize, compare: &F, leftright: Ordering, rightleft: Ordering)
    where
        F: Fn(&T, &T) -> Ordering
{
    // The slice to be sorted is divided into S0 | L | M | R | S1
    // The indexes into the slice are l0, l1, r0, r1
    let mut l0 = 0;
    let mut l1 = split;
    let mut r0 = split;
    let mut r1 = s.len();

    let llen = l1 - l0;
    let rlen = r1 - r0;

    if llen == 0 || rlen == 0 {
        return;
    }
    // When llen == 1 the code below performs the same number of comparisons and moves
    // if llen == 1 {
    //     // |L| = 1: Just insert it into R
    //     let pos = insertion_point(&s[l0], &s[r0 .. r1], compare, leftright);
    //     rotate(&mut s[l0 .. r0 + pos], pos);
    //     return;
    // }
    if rlen == 1 {
        // |R| = 1: Just insert it into L
        let pos = insertion_point(&s[r0], &s[l0 .. l1], compare, rightleft);
        rotate(&mut s[l0 + pos .. r1], 1);
        return;
    }

    // R may contain values that are higher than l_max.  These values are already in their final
    // position, so we can move them from R to S1.
    let pos = insertion_point(&s[l1 - 1], &s[r0 .. r1], compare, leftright);
    if pos == 0 {
        // l_max < r_0 -> L-R is already sorted
        //
        // Although this code is shrinking the size of the sequence and setting up a useful
        // invariant, it also provides a third behaviour which is useful when this function is
        // called as part of a mergesort, which typically merges blocks of size 2^n.
        // Since that is one more 2^n - 1, the size of a balanced binary tree, `split_biased` must
        // use a tree of size 2^(n+1) - 1, and since it is biased to the left, only one comparison
        // is required to check the value against the first point of the sequence.
        //
        // See the test `bisect_2pow` for an example.  In the test, /some/ of the paths must
        // require 5 comparisons.  We bias the algorithm so that one common path is significantly
        // advantaged at the cost of /all/ other paths requiring 5 comparisons.
        //
        // This means already ordered sequences are merged with one comparison, and an entire
        // mergesort of already ordered data will take the minimum possible (n-1) comparisons.
        // This is useful because much real data is close to already sorted, so optimising this
        // case is valuable.  Many other real-world sorts special-case for already sorted data,
        // often at the cost of worst-case performance for randomly ordered data.  In our case, the
        // single comparison is performed without affecting the worst-case performance on random
        // data.
        return;
    }
    r1 = r0 + pos;
    // l_max is largest value

    // L may contain values that are lower than r_0.  These values are already in their final
    // position, so we can move them from L to S0.  Note, we ignore l_max since we know it is
    // larger than r_0.  This is why we don't need to test whether |L| = 0.
    let pos = insertion_point(&s[r0], &s[l0 .. l1 - 1], compare, rightleft);
    l0 += pos;
    // r0 is smallest value

    if l1 - l0 == 1 || r1 - r0 == 1 {
        // since r_0 is smallest value, if |R| = 1, we just need to swap L and R
        // since l_max is largest value, if |L| = 1, we just need to swap L and R
        rotate(&mut s[l0 .. r1], r1 - r0);
        return;
    }

    loop {
        // At this point, we have several invariants:
        debug_assert!(compare(&s[l0], &s[r0]) != Ordering::Less);           // 1. r_0 is min value
        debug_assert!(compare(&s[r1 - 1], &s[l1 - 1]) != Ordering::Greater);// 2. l_max is max value
        debug_assert!(l1 - l0 > 1);                                         // 3. |L| > 1
        debug_assert!(l1 == r0);                                            // 4. M is empty
        debug_assert!(r1 - r0 > 1);                                         // 5. |R| > 1

        // One or more elements at the start of R are smaller than L.  Find out how many elements,
        // and move them to the space at the start of L. Shift all the L elements to the right.
        // S0 | L | R | S1 - split R < l_0
        // S0 | L | R0 | R1 | S1 - split L < R1_0
        // S0 | L0 | L1 | R0 | R1 | S1 - rotate L0-L1-R0 to R0-L0-L1
        // S0 | R0 | L0 | L1 | R1 | S1 - R0 and L0 are in order, add to S0; L1 becomes M
        // S0 | L1 | R1 | S1 - R0 and L0 are in order, add to S0
        let pos = insertion_point(&s[l0], &s[r0 + 1 .. r1], compare, leftright);
        let rsplit = r0 + 1 + pos;
        if rsplit == r1 {
            // all of R < all of L
            rotate(&mut s[l0 .. r1], r1 - r0);
            return;
        }
        // from above we know that l_0 < r_split, and invariant l_max > r_* still holds,
        // so we can take off the two endpoints of L
        debug_assert!(l0 + 1 <= l1 - 1);  // invariant |L| > 1 must be true
        let pos = insertion_point(&s[rsplit], &s[l0 + 1 .. l1 - 1], compare, rightleft);
        let lsplit = l0 + 1 + pos;
        rotate(&mut s[l0 .. rsplit], rsplit - r0);
        l0 = lsplit + rsplit - r0;  // add R0 and L0 to S0
        r0 = rsplit;
        l1 = r0;
        if l1 - l0 == 1 || r1 - r0 == 1 {
            // since r_0 is smallest value, if |R| = 1, we just need to swap L and R
            // since l_max is largest value, if |L| = 1, we just need to swap L and R
            rotate(&mut s[l0 .. r1], r1 - r0);
            return;
        }
    }
}

pub fn sort_by<T, F>(s: &mut [T], compare: &F)
    where
        F: Fn(&T, &T) -> Ordering
{
    let length = s.len();
    let mut blk = 1;
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
        assert_eq!(count.get(), s.len() - 1);
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
        assert_eq!(count.get(), 4);
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
        assert_eq!(count.get(), 4);
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

    #[test]
    fn bisect_0() {
        assert_eq!(super::insertion_point(&Nc(3), &[], &Nc::cmp, Ordering::Less), 0)
    }

    #[test]
    fn bisect_1_before() {
        assert_eq!(super::insertion_point(&Nc(1), &[Nc(2)], &Nc::cmp, Ordering::Less), 0)
    }
    #[test]
    fn bisect_1_after() {
        assert_eq!(super::insertion_point(&Nc(3), &[Nc(2)], &Nc::cmp, Ordering::Less), 1)
    }

    #[test]
    fn bisect_2_before() {
        assert_eq!(super::insertion_point(&Nc(1), &[Nc(2), Nc(4)], &Nc::cmp, Ordering::Less), 0)
    }
    #[test]
    fn bisect_2_middle() {
        assert_eq!(super::insertion_point(&Nc(3), &[Nc(2), Nc(4)], &Nc::cmp, Ordering::Less), 1)
    }
    #[test]
    fn bisect_2_after() {
        assert_eq!(super::insertion_point(&Nc(5), &[Nc(2), Nc(4)], &Nc::cmp, Ordering::Less), 2)
    }

    #[test]
    fn bisect_3_before() {
        assert_eq!(super::insertion_point(&Nc(1), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp, Ordering::Less), 0)
    }
    #[test]
    fn bisect_3_lt() {
        // Use less-than if the value should be inserted before equal values
        assert_eq!(super::insertion_point(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp, Ordering::Less), 1)
    }
    #[test]
    fn bisect_3_le() {
        // Use less-than-or-equal if value should be inserted after equal values
        assert_eq!(super::insertion_point(&Nc(4), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp, Ordering::Greater), 2)
    }
    #[test]
    fn bisect_3_after() {
        assert_eq!(super::insertion_point(&Nc(7), &[Nc(2), Nc(4), Nc(6)], &Nc::cmp, Ordering::Less), 3)
    }

    #[test]
    fn bisect_2powm1() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::insertion_point(&v, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less), v);
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
            assert_eq!(super::insertion_point(&v, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less), v);
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
            assert_eq!(super::insertion_point(&v, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5])
    }

    #[test]
    fn bisect_20() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::insertion_point(&v, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![2, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5])
    }

    #[test]
    fn bisect_21() {
        let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];
        let mut profile = Vec::new();
        for v in 0 .. s.len() + 1 {
            let count = Cell::new(0);
            assert_eq!(super::insertion_point(&v, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Less), v);
            profile.push(count.get());
        }
        assert_eq!(profile, vec![3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5])
    }

    #[test]
    fn bisect_unstable() {
        // If Ordering::Equal passed, then insertion point returned on first match
        // Here we have 2^n -1 values, so first test will be in middle. Since that matches the
        // value, it will return immediately.
        let s = [1, 5, 5, 5, 5, 5, 8];
        let count = Cell::new(0);
        super::insertion_point(&5, &s, &|&a, &b|{count.set(count.get() + 1); a.cmp(&b)}, Ordering::Equal);
        assert_eq!(count.get(), 1);
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
