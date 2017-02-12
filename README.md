# gidsort
Non-allocating in-place stable mergesort

Mergesort is a very pleasant sorting algorithm, providing a stable sort with O(n log n) performance if we allow O(n) memory usage.

For very large n, we'd prefer to have something less than O(n) memory use.
Ideally, we'd get O(1) memory usage while keeping the stability and O(n log n) performance.
O(1) means the algorithm uses a fixed amount of memory (variables and stack) independent of the size of the structure to be sorted.
Sorts with O(1) memory use are called in-place sorts.

Most attempts to create an in-place mergesort either lose the property of stability, fail to sort for some patterns, or reach a point where the constants for the complexity values are too high to be practical.

A common pattern for in-place mergesorts is to break the structure into √n sized blocks and move the highest values to one end to create a workspace with which to perform a standard merge on each block.

The algorithm here avoids that approach, and starts with the observation that for a merge of two sorted sequences L = {L<sub>0</sub>...l<sub>|L|</sub>} and R = {R<sub>0</sub>...r<sub>|R|</sub>}:

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

However, this breaks the invariant that R is sorted. So we introduce a new block M to hold the smallest values of L:

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

But eventually we break the invariant that M must be sorted:

| S | L | M | R |
|---|---|---|---|
| 1 2 3 4 | 10 | 8 6 | 5 7 9 |

So, we don't want to do the previous step.

| S | L | M | R |
|---|---|---|---|
| 1 2 3 | 8 10 | 4 6 | 5 7 9 |

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
