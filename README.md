# gidsort
Non-allocating in-place stable mergesort

Mergesort is a very pleasant sorting algorithm, providing a stable sort with O(n log n) performance if we allow O(n) memory usage.

For very large n, we'd prefer to have something less than O(n) memory use.
Ideally, we'd get O(1) memory usage while keeping the stability and O(n log n) performance.
O(1) means the algorithm uses a fixed amount of memory (variables and stack) independent of the size of the structure to be sorted.
Sorts with O(1) memory use are called in-place sorts.

Most attempts to create an in-place mergesort either lose the property of stability, fail to sort for some patterns, or reach a point where the constants for the complexity values are too high to be practical.

A common pattern for in-place mergesorts is to break the structure into √n sized blocks and move the highest values to one end to create a workspace with which to perform a standard merge on each block.

The algorithm here avoids that approach, and starts with the observation that for a merge of two ordered sequences L = {L<sub>0</sub>...l<sub>|L|</sub>} and R = {R<sub>0</sub>...r<sub>|R|</sub>}:

| S |      L      |   R   |
|---|-------------|-------|
|   | 1 2 3 7 8 9 | 4 5 6 |

the first value in the merged sequence is either L<sub>0</sub> or R<sub>0</sub>.  While it is L<sub>0</sub> we can simply change our boundaries to indicate that the sequence is merged:

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 3 | 7 8 9 | 4 5 6 |

When the lowest value is R<sub>0</sub>, we must move R<sub>0</sub> to the location occupied by L<sub>0</sub>. The simplest way to do that is to swap L<sub>0</sub> and R<sub>0</sub>.

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 3 | 4 8 9 | 7 5 6 |

However, this breaks the invariant that R is ordered. So we introduce a new block M to hold the smallest values of L. This block has the invariants that it is always ordered and all values in M are before all values in L:

| S |      L      |   M | R   |
|---|-------------|---|-----|
| 1 2 3 4 | 8 9 | 7 | 5 6 |

Since M represents the lower values of L, while M exists, we need to compare M<sub>0</sub> and R<sub>0</sub> and continue swapping if necessary:

| S |      L      |   M | R   |
|---|-------------|---|-----|
| 1 2 3 4 5 6 | | 7 8 9 | |

If M+L or R become empty, the merge is finished.

Works great! And it took only 6 comparisons and 3 swaps to merge 9 values. Nice!  Our stable in-place mergesort is well on its way to O(n log n) performance.

Except this particular sequence had no point where M<sub>0</sub> held the lowest unmerged value.

That's where it gets tricky.

Let's try with:

| S |      L      |   R   |
|---|-------------|-------|
|   | 2 4 6 8 10 | 1 3 5 7 9 |

| S | L | M | R |
|---|---|---|---|
| 1 | 4 6 8 10 | 2 | 3 5 7 9 |

We can keep going, swapping L<sub>0</sub> and M<sub>0</sub> for a little while, but

| S | L | M | R |
|---|---|---|---|
| 1 2 | 6 8 10 | 4 | 3 5 7 9 |

| S | L | M | R |
|---|---|---|---|
| 1 2 | 6 8 10 | 4 | 3 5 7 9 |

| S | L | M | R |
|---|---|---|---|
| 1 2 3 | 8 10 | 4 6 | 5 7 9 |

But eventually we break the invariant that M must be ordered:

| S | L | M | R |
|---|---|---|---|
| 1 2 3 4 | 10 | 8 6 | 5 7 9 |

Consider an algorithm to merge M and R into the space to the left of L.

First, split R into X and RZ where X contains all values less than M<sub>0</sub>.
Then, split M into Y and MZ where Y contains all values less than RZ<sub>0</sub>.
Now, split L into L<sub>X</sub>, L<sub>Y</sub>, and LZ, where |L<sub>X</sub>| = |X| and |L<sub>Y</sub>| = |Y|.

| S | L | M | R |
|---|---|---|---|
| S | L<sub>X</sub> - L<sub>Y</sub> - LZ | Y - M | X - R |

We want to end up with X and Y appended to S, and our invariants kept: L, M, and R still ordered and M < L.  There are 4 reconfigurations that give this:

1. 
   | S | L | M | R |
   |---|---|---|---|
   | S - X - Y | M - L<sub>X</sub> - L<sub>Y</sub> - LZ | | R |

1. 
   | S | L | M | R |
   |---|---|---|---|
   | S - X - Y | L<sub>X</sub> - L<sub>Y</sub> - LZ | M | R |

1. 
   | S | L | M | R |
   |---|---|---|---|
   | S - X - Y | L<sub>Y</sub> - LZ | M - L<sub>X</sub> | R |

1. 
   | S | L | M | R |
   |---|---|---|---|
   | S - X - Y | LZ | M - L<sub>X</sub> - L<sub>Y</sub> | R |

(Note, the 5th reconfiguration where all L elements move to M degenerates back to the first case, since if |L| == 0, we always rename M as L).

(Note, the rest of this document is still in draft format)

```
A. S0 - S1 / M - L0 - L1 - L

- only solution that eliminates M
- more expensive than C
- use if |L| <= x + 2y and |L| + |M| + x - y < |L| (never, since y <= |M|)

1.
- swap L0 - S0
        d = 2x, f = x, c = x
- rot L1 - L - S1 - M - L0 -> S1 - M - L0 - L1 - L
        d = |L| + |M|, f = y, c = |L| + |M| - y
- total cost: |L| + |M| + x - y

B. S0 - S1 / L0 - L1 - L / M

- more expensive than A and C

1.
- rot S1 - M - S0 -> S0 - S1 - M
        d = |M| + x, f = 0, c = |M| + x
- rot L0 - L1 - L - S0 - S1 -> S0 - S1 - L0 - L1 - L
        d = |L| + x + y, f = x + y, c = |L|
- total cost: |L| + |M| + x

C. S0 - S1 / L1 - L / M - L0

- cheaper than 1 and 2
- works if |L| >= x (if |L| == x, then M becomes L)
- use if |L| < |M| + 2x + y
- if |L| < x:
        - swap L - S0a
                d = 2|L|, f = |L|, c = |L|
        - rotate S1 - M - L - S0b to S0b - S1 - M - L
                d = |M| + x, f = x - |L|, c = |M| + |L|
        - total cost: 2|L| + |M|
        - S0 S1 M L R
        - eliminates M
        OR
        - rotate L - S1 - M - S0 to S0 - L - S1 - M
                d = |L| + |M| + x, f = x, c = |L| + |M|
        - rotate L - S1 to S1 - L
                d = |L| + y, f = y, c = |L|
        - total cost: 2|L| + |M|
        - S0 S1 L M R
        OR
        - rotate L - S1 - M - S0 to S0 - L - S1 - M
                d = |L| + |M| + x, f = x, c = |L| + |M|
        - rotate L - S1 - M to S1 - M - L
                d = |L| + |M|, f = y, c = |L| + |M| - y
        - total cost 2|L| + 2|M| - y > 2|L| + |M|
        OR
        - rotate S1 - M - S0 to S0 - S1 - M
                d = |M| + x, f = 0, c = |M| + x
        - rotate L - S0 - S1 to S0 - S1 - L
                d = |L| + x + y, f = x + y, c = |L|
        - total cost: |L| + |M| + x > 2|L| + |M|

1.
- swap L0 - S0
        d = 2x, f = x, c = x
- rot L1 - L - S1 -> S1 - L1 - L
        d = |L| - x + y, f = y, c = |L| - x
- total cost: |L|

D. S0 - S1 / L / M - L0 - L1

- only solution where L does not move
- option 2 possibly more efficient due to single swap

1.
- swap L0 - S0
        d = 2x, f = x, c = x
- swap L1 - S1
        d = 2y, f = y, c = y
- rot L1 - M - L0 to M - L0 - L1
        d = |M| + x, f = 0, c = |M| + x
- total cost: |M| + 2x + y

2.
- rot S1 - M - S0 to M - S0 - S1
        d = |M| + x, f = 0, c = |M| + x
- swap L0/L1 - S0/S1
        d = 2x + 2y, f = x + y, c = x + y
- total cost: |M| + 2x + y

3.
- swap L0 - S0
        d = 2x, f = x, c = x
- rot S1 - M - L0 to M - L0 - S1
        d = |M| + x, f = 0, c = |M| + x
- swap L1 - S1
        d = 2y, f = y, c = y
- total cost = |M| + 2x + y

4.
- swap L1 - S1
        d = 2x, f = x, c = x
- rot L1 - M - S0 to M - S0 - L1
        d = |M| + x, f = 0, c = |M| + x
- swap L0 - S0
        d = 2y, f = y, c = y
- total cost = |M| + 2x + y

Final algorithm:

if |L| < x:
        - swap L - S0a
        - rot S1 - M - L - S0b to S0b - S1 - M - L
        - M L
else if |L| < |M| + 2x + y:
        - swap L0 - S0
        - rot L1 - L - S1 -> S1 - L1 - L
        - L1 L / M L0
else:
        - rot S1 - M - S0 to M - S0 - S1
        - swap L0/L1 - S0/S1
        - L / M L0 L1

Note, since first test and clause do not split S1 - M, we can check for this
after finding x, and then search all of M-L for new split point, rather than
just M
```



Older notes:




When we move M<sub>0</sub> out, a gap opens between L and M. We could:

1. Shift L right, opening a gap to insert M<sub>0</sub>

	| S | L | M | R |
	|---|---|---|---|
	| 1 2 3 4 | 8 10 | 6 | 5 7 9 |

	This solution moves |L| values.
	(Note, to measure the cost, count the total number of moves of a value from its original position but subtract the number of values moved into their final position.
	Hence, in this case, we ignore the move of M<sub>0</sub> to its final location.)

2. Shift M left one space, opening a gap at end of M to insert L<sub>0</sub>

	| S | L | M | R |
	|---|---|---|---|
	| 1 2 3 4 | 10 | 6 8 | 5 7 9 |

	This solution moves |M| values (|M| values from M + 1 value from L, minus one value (M<sub>0</sub> placed into final position)s.

3. Rotate M and L to recombine as a single L

	| S | L | M | R |
	|---|---|---|---|
	| 1 2 3 4 | 6 8 10 | | 5 7 9 |

	This solution moves |L| + |M| - 1 values, but:
	- removes M, allowing the algorithm to run more efficiently for a few steps, and
	- may also place a few additional values in their final place, i.e. all the M values that are less than R<sub>0</sub>

4. Swap all of M with the prefix of L

	| S | L | M | R |
	|---|---|---|---|
	| 1 2 3 | 4 6 | 8 10 | 5 7 9 |

	This solution moves 2|M| - 1 values, with the second advantage from solution 3. If |L| <= |M|, use solution 3 instead.  Note, this is the operation performed above when |M| = 1.

5. Partition M by R<sub>0</sub>, perform solution 4 on the left partition of M, and shift the rest of M down to make room for L.

	| S | L | M | R |
	|---|---|---|---|
	| 1 2 3 4 | 10 | 6 8 | 5 7 9 |

	This solution moves |M| values, and provides the information that R<sub>0</sub> is the next lowest value.

	It does require additional comparisons of R<sub>0</sub> with M. However, these comparisons would likely be done later, as M and R continued to be compared.

6. Partition M by R<sub>0</sub>, and shift L right to make space for the left partition of M.

	| S | L | M | R |
	|---|---|---|---|
	| 1 2 3 4 | 10 | 6 8 | 5 7 9 |

	This solution moves |L| values, and provides the information that R<sub>0</sub> is the next lowest value.


7. Select 5 and 6 based on the relative lengths of L and M.

After solutions 5, 6, and 7 we now know that R<sub>0</sub> < M<sub>0</sub>. We can search for M<sub>0</sub> in R to speed up swapping.

Splitting the blocks this way allows us to use binary search to find the location of M<sub>0</sub> in R or vice versa.

So, we can switch back and forth between the M and R blocks, terminating when one of the blocks is empty.  (It is also possible for L to become empty first, in which case we relabel M as L and continue).

An additional possibility: when we search for R<sub>0</sub> in M using binary search, actually search M-L and perform different steps if the insertion point is found in L.
