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

First, split R into X and R' where X contains all values less than M<sub>0</sub>.
Then, split M into Y and M' where Y contains all values less than R'<sub>0</sub>.
Now, split L into L<sub>X</sub>, L<sub>Y</sub>, and L', where |L<sub>X</sub>| = |X| and |L<sub>Y</sub>| = |Y|.

| S | L | M | R |
|---|---|---|---|
| S | L<sub>X</sub> - L<sub>Y</sub> - L' | Y - M' | X - R' |

We want to end up with X and Y appended to S, and our invariants kept: each of L, M, and R ordered internally and M < L.  There are 4 reconfigurations that give this:

1.
   | S | L | M | R |
   |---|---|---|---|
   | S - X - Y | M' - L<sub>X</sub> - L<sub>Y</sub> - L' | | R' |

1.
   | S | L | M | R |
   |---|---|---|---|
   | S - X - Y | L<sub>X</sub> - L<sub>Y</sub> - L' | M' | R' |

1.
   | S | L | M | R |
   |---|---|---|---|
   | S - X - Y | L<sub>Y</sub> - L' | M' - L<sub>X</sub> | R' |

1.
   | S | L | M | R |
   |---|---|---|---|
   | S - X - Y | L' | M' - L<sub>X</sub> - L<sub>Y</sub> | R' |

   Note, this is the only reconfiguration where L' stays in the same location.

(Note, the 5th reconfiguration where all L elements move to M degenerates back to the first case, since if |L| == 0, we always rename M as L).

There are multiple ways to achieve these reconfigurations.
We initially limit ourselves to two operations:

1. swap of two equal-sized but possibly disjoint sequences, and
2. rotation, i.e. swapping two possibly unequal-sized but adjacent blocks.

Method A:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L<sub>X</sub> - L<sub>Y</sub> - L' - Y - M' - X - R' | rotate Y - M' - X to M' - X - Y | \|M\| + \|X\| | 0 | \|M\| + \|X\| |
| L<sub>X</sub> - L<sub>Y</sub> - L' - M' - X - Y - R' | swap L<sub>X</sub> - L<sub>Y</sub> with X - Y | 2\|X\| + 2\|Y\| | \|X\| + \|Y\| | \|X\| + \|Y\| |
| X - Y - L' - M' - L<sub>X</sub> - L<sub>Y</sub> - R' | = reconfiguration 4 | | total = | \|M\| + 2\|X\| + \|Y\| |

- works for |L| >= |X| + |Y|

Method B:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L<sub>X</sub> - L<sub>Y</sub> - L' - Y - M' - X - R' | swap L<sub>X</sub> with X | 2\|X\| | \|X\| | \|X\| |
| X - L<sub>Y</sub> - L' - Y - M' - L<sub>X</sub> - R' | rotate L<sub>Y</sub> - L' - Y to Y - L<sub>Y</sub> - L' | \|Y\| + (\|L\| - \|X\| - \|Y\|) + \|Y\| | \|Y\| | \|L\| - \|X\| |
| X - Y - L<sub>Y</sub> - L' - M' - L<sub>X</sub> - R' | = reconfiguration 3 | | total = | \|L\| |

- fewer moves than Method A if:
	|L| < |M| + 2|X| + |Y|
- works for |L| >= |X|

Method C:

If |L| < |X|, split X into X' and X'' such that |X'| = |L|:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L - Y - M' - X' - X'' - R' | swap L with X' | 2\|L\| | \|L\| | \|L\| |
| X' - Y - M' - L - X'' - R' | rotate Y - M' - L - X'' to X'' - Y - M' - L | \|M\| + \|L\| + (\|X\|- \|L\|) | (\|X\| - \|L\|) + \|Y\| | \|L\| + \|M\| - \|Y\| |
| X' - X'' - Y - M' - L - R' | = reconfiguration 1 | | total = | 2\|L\| + \|M\| - \|Y\| |

- eliminates M, since M' - L can be remerged as L
- fewer moves than Method A if:
	- 2|L| + |M| - |Y| < |M| + 2|X| + |Y|
	- 2|L| - |Y| < 2|X| + |Y|
	- 2|L| < 2|X| + 2|Y|
	- |L| < |X| + |Y|
- fewer moves than Method B if:
	- 2|L| + |M| - |Y| < |L|
	- |L| + |M| - |Y| < 0
	- |L| + |M| < |Y|
	- Since |Y| <= |M|, never, so this is only useful when other methods do not work (i.e |L| < |X|)


Final algorithm:

```
if |L| < |X|:
	Method C
else if |L| < |M| + 2|X| + |Y|:
	Method B
else:
	Method A
```

Note, since first test and method C do not split Y - M', we can perform Method C
after finding |X|, and then search all of M-L for new split point, rather than
just M.  (This may not be a good idea after the next step).




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
