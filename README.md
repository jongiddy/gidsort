# gidsort
Non-allocating in-place stable mergesort

Mergesort is a very pleasant sorting algorithm, providing a stable sort with O(n log n) performance if we allow O(n) memory usage.

For very large n, we'd prefer to have something less than O(n) memory use.
Ideally, we'd get O(1) memory usage while keeping the stability and O(n log n) performance.
O(1) means the algorithm uses a fixed amount of memory (variables and stack) independent of the size of the structure to be sorted.
Sorts with O(1) memory use are called in-place sorts.

Most attempts to create an in-place mergesort either lose the property of stability, fail to sort for some patterns, or reach a point where the constants for the complexity values are too high to be practical.

A common pattern for in-place mergesorts is to break the structure into √n sized blocks and move the highest values to one end to create a workspace with which to perform a standard merge on each block.

The algorithm here avoids that approach, and starts with the observation that for a merge of two ordered sequences L = {L<sub>0</sub>...l<sub>|L|-1</sub>} and R = {R<sub>0</sub>...r<sub>|R|-1</sub>}:

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

First, split R into X and R' where X contains all values of R less than M<sub>0</sub>.
Then, split M into Y and M' where Y contains all values of M less than R'<sub>0</sub>.
Now, split L into L<sub>X</sub>, L<sub>Y</sub>, and L', where |L<sub>X</sub>| = |X| and |L<sub>Y</sub>| = |Y|.

| S | L | M | R |
|---|---|---|---|
| S | L<sub>X</sub> - L<sub>Y</sub> - L' | Y - M' | X - R' |

We want to end up with X and Y appended to S, and our invariants kept: each of L, M, and R ordered internally and M < L.  There are 4 reconfigurations that give this:

Configuration 1:

| S | L | M | R |
|---|---|---|---|
| S - X - Y | M' - L<sub>X</sub> - L<sub>Y</sub> - L' | | R' |

Note, this configuration eliminates M.

Configuration 2:

| S | L | M | R |
|---|---|---|---|
| S - X - Y | L<sub>X</sub> - L<sub>Y</sub> - L' | M' | R' |

Configuration 3:

| S | L | M | R |
|---|---|---|---|
| S - X - Y | L<sub>Y</sub> - L' | M' - L<sub>X</sub> | R' |

Configuration 4:

| S | L | M | R |
|---|---|---|---|
| S - X - Y | L' | M' - L<sub>X</sub> - L<sub>Y</sub> | R' |

Note, this is the only reconfiguration where L' stays in the same location.

(Note, the 5th reconfiguration where all L elements move to M degenerates back to the first case, since if |L| == 0, we always rename M as L).

There are multiple ways to achieve these reconfigurations.
We initially limit ourselves to two operations:

1. swap of two equal-sized but possibly disjoint sequences, and
2. rotation, i.e. swapping two possibly unequal-sized but adjacent blocks.

Method A1:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L<sub>X</sub> - L<sub>Y</sub> - L' - Y - M' - X - R' | rotate Y - M' - X to M' - X - Y | \|M\| + \|X\| | 0 | \|M\| + \|X\| |
| L<sub>X</sub> - L<sub>Y</sub> - L' - M' - X - Y - R' | swap L<sub>X</sub> - L<sub>Y</sub> with X - Y | 2\|X\| + 2\|Y\| | \|X\| + \|Y\| | \|X\| + \|Y\| |
| X - Y - L' - M' - L<sub>X</sub> - L<sub>Y</sub> - R' | = reconfiguration 4 | | total = | \|M\| + 2\|X\| + \|Y\| |

- works for |L| >= |X| + |Y|

Method A2:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L<sub>X</sub> - L<sub>Y</sub> - L' - Y - M' - X - R' | swap L<sub>X</sub> with X | 2\|X\| | \|X\| | \|X\| |
| X - L<sub>Y</sub> - L' - Y - M' - L<sub>X</sub> - R' | rotate L<sub>Y</sub> - L' - Y to Y - L<sub>Y</sub> - L' | \|Y\| + (\|L\| - \|X\| - \|Y\|) + \|Y\| | \|Y\| | \|L\| - \|X\| |
| X - Y - L<sub>Y</sub> - L' - M' - L<sub>X</sub> - R' | = reconfiguration 3 | | total = | \|L\| |

- fewer moves than Method A1 if:
	|L| < |M| + 2|X| + |Y|
- works for |L| >= |X|

Method A3:

If |L| < |X|, split X into X' and X'' such that |X'| = |L|:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L - Y - M' - X' - X'' - R' | swap L with X' | 2\|L\| | \|L\| | \|L\| |
| X' - Y - M' - L - X'' - R' | rotate Y - M' - L - X'' to X'' - Y - M' - L | \|M\| + \|L\| + (\|X\|- \|L\|) | (\|X\| - \|L\|) + \|Y\| | \|L\| + \|M\| - \|Y\| |
| X' - X'' - Y - M' - L - R' | = reconfiguration 1 | | total = | 2\|L\| + \|M\| - \|Y\| |

- eliminates M, since M' - L can be remerged as L
- fewer moves than Method A1 if:
	- 2|L| + |M| - |Y| < |M| + 2|X| + |Y|
	- 2|L| - |Y| < 2|X| + |Y|
	- 2|L| < 2|X| + 2|Y|
	- |L| < |X| + |Y|
- fewer moves than Method A2 if:
	- 2|L| + |M| - |Y| < |L|
	- |L| + |M| - |Y| < 0
	- |L| + |M| < |Y|
	- Since |Y| <= |M|, never, so this is only useful when other methods do not work (i.e |L| < |X|)


Algorithm A:

```
if |L| < |X|:
	Method A3
else if |L| < |M| + 2|X| + |Y|:
	Method A2
else:
	Method A1
```

If the insertion point for R'<sub>0</sub> is found inside M (not at the end of M), i.e. |Y| < |M|, then after the reconfiguration, we know that R<sub>0</sub> is the minimum value remaining in the unsorted values.
Keeping this information available for the next iteration requires either a flag or for this information to be a loop invariant.
Setting the loop invariant up allows us to move initial values in L that are already in place straight to S, so a loop invariant sounds good.

There are some special cases to consider.

If |X| == |R| (M<sub>0</sub> > R<sub>i</sub> for all i), then we simply need to reconfigure L - M - R to R - M - L as a final step to fully merged sequences.

Method B1:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L - M - R | rotate L - M to M - L | \|L\| + \|M\| | 0 | \|L\| + \|M\| |
| M - L - R | rotate M - L - R to R - M - L | \|M\| + \|L\| + \|R\| | \|M\| + \|L\| + \|R\| | 0 |
| R - M - L | | | total = | \|L\| + \|M\| |

Method B2:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L - M - R | rotate M - R to R - M | \|M\| + \|R\| | 0 | \|M\| + \|R\| |
| L - R - M | rotate L - R - M to R - M - L | \|L\| + \|R\| + \|M\| | \|L\| + \|R\| + \|M\| | 0 |
| R - M - L | | | total = | \|M\| + \|R\| |

- fewer moves than Method B1 if:
	- \|M\| + \|R\| < \|L\| + \|M\|
	- \|R\| < \|L\|


Algorithm B:

```
find X in R where X[i] < M[0]
if |X| == |R|:
	if |L| < |R|:
		Method B1
	else:
		Method B2
	merge completed
else:
	find Y in M where Y[i] < R'[0]
	if |L| < |X|:
		Method A3
	else if |L| < |M| + 2|X| + |Y|:
		Method A2
	else:
		Method A1
```


If |Y| == |M| (R'<sub>0</sub> > M<sub>i</sub> for all i), then M will be eliminated and the loop invariant does not necessarily hold.
We need to search for R'<sub>0</sub> in L as well to keep the invariant.
Hence, we need to consider different approaches for dealing with this case.

To represent this case, remove M' and add Z, where Z contains all values of L less than R'<sub>0</sub>.

| S | L | M | R |
|---|---|---|---|
| S | Z - L<sub>X</sub> - L<sub>Y</sub> - L' | Y | X - R' |

We want to end up with X, Y, and Z appended to S, and our invariants kept: each of L, M, and R ordered internally and M < L.  There are 3 reconfigurations that give this:

Configuration 5:

| S | L | M | R |
|---|---|---|---|
| S - X - Y - Z | L<sub>X</sub> - L<sub>Y</sub> - L' | | R' |

Configuration 6:

| S | L | M | R |
|---|---|---|---|
| S - X - Y - Z | L<sub>Y</sub> - L' | L<sub>X</sub> | R' |

Configuration 7:

| S | L | M | R |
|---|---|---|---|
| S - X - Y - Z | L' | L<sub>X</sub> - L<sub>Y</sub> | R' |

Method C1:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| Z - L<sub>X</sub> - L<sub>Y</sub> - L' - Y - X - R' | rotate Y - X to X - Y | \|X\| + \|Y\| | 0 | \|X\| + \|Y\| |
| Z - L<sub>X</sub> - L<sub>Y</sub> - L' - X - Y - R' | rotate Z - L<sub>X</sub> - L<sub>Y</sub> - L' - X - Y to X - Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L'  | \|Z\| + \|X\| + \|Y\| + (\|L\| - \|X\| - \|Y\| - \|Z\|) + \|X\| + \|Y\| | \|X\| + \|Y\| + \|Z\| | \|L\| - \|Z\| |
| X - Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L' - R' | = reconfiguration 5 | | total = | \|L\| + \|X\| + \|Y\| - \|Z\| |

- eliminates M
- works for all |L|

Method C2:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| Z - L<sub>X</sub> - L<sub>Y</sub> - L' - Y - X - R' | rotate Z - L<sub>X</sub> - L<sub>Y</sub> - L' - Y to Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L' | \|Z\| + \|X\| + \|Y\| + (\|L\| - \|X\| - \|Y\| - \|Z\|) + \|Y\| | 0 | \|L\| + \|Y\| |
| Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L' - X - R' | rotate Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L' - X to X - Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L'  | \|Y\| + \|Z\| + \|X\| + \|Y\| + (\|L\| - \|X\| - \|Y\| - \|Z\|) + \|X\| | \|X\| + \|Y\| + \|Z\| | \|L\| - \|Z\| |
| X - Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L' - R' | = reconfiguration 5 | | total = | 2\|L\| + \|Y\| - \|Z\| |

- eliminates M
- fewer moves than Method C1 if:
	- 2|L| + |Y| - |Z| < |L| + |X| + |Y| - |Z|
	- 2|L| < |L| + |X|
	- |L| < |X|
- works for all |L|

Method C3:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| Z - L<sub>X</sub> - L<sub>Y</sub> - L' - Y - X - R' | rotate Y - X to X - Y | \|X\| + \|Y\| | 0 | \|X\| + \|Y\| |
| Z - L<sub>X</sub> - L<sub>Y</sub> - L' - X - Y - R' | rotate Z - L<sub>X</sub> - L<sub>Y</sub> to L<sub>X</sub> - L<sub>Y</sub> - Z | \|Z\| + \|X\| + \|Y\| | \|Z\| | \|X\| + \|Y\| |
| L<sub>X</sub> - L<sub>Y</sub> - Z - L' - X - Y - R' | swap L<sub>X</sub> - L<sub>Y</sub> with X - Y | 2\|X\| + 2\|Y\| | \|X\| + \|Y\| | \|X\| + \|Y\| |
| X - Y - Z - L' - L<sub>X</sub> - L<sub>Y</sub> - R' | = reconfiguration 7 | | total = | 3\|X\| + 3\|Y\| |

- requires |L| >= |X| + |Y| + |Z|
- fewer moves than Method C1 if:
	- 3|X| + 3|Y| < |L| + |X| + |Y| - |Z|
	- 2|X| + 2|Y| < |L| - |Z|
	- 2|X| + 2|Y| + |Z| < |L|
	- |L| > 2|X| + 2|Y| + |Z|
- fewer moves than Method C2 if:
	- 3|X| + 3|Y| < 2|L| + |Y| - |Z|
	- 3|X| + 2|Y| < 2|L| - |Z|
	- 3|X| + 2|Y| + |Z| < 2|L|
	- 1.5|X| + |Y| + 0.5|Z| < |L|
	- |L| > 1.5|X| + |Y| + 0.5|Z|

Algorithm C:

```
find X in R where X[i] < M[0]
if |X| == |R|:
	if |L| < |R|:
		Method B1
	else:
		Method B2
	merge completed
else:
	find Y in M where Y[i] < R'[0]
	if |Y| == |M|:
		find Z in L where Z[i] < R'[0]
		if |L| < |X|:
			Method C2
		elif |L| < 2|X| + 2|Y| + |Z|
			Method C1
		else:
			Method C3
	else:
		if |L| < |X|:
			Method A3
		else if |L| < |M| + 2|X| + |Y|:
			Method A2
		else:
			Method A1
```

We do not need to handle the case where |Z| == |L| (i.e. R'<sub>0</sub> > L<sub>i</sub> for all i). This can never occur since L<sub>|L|-1</sub> is the largest value.

However, we can consider |Z| == 0 as a special case.

We need to reconfigure L - Y - X - R' to X - Y - L - R' as a final step to fully merged sequences.

Method D1:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L<sub>X</sub> - L<sub>Y</sub> - L' - Y - X - R' | rotate Y - X to X - Y | \|X\| + \|Y\| | 0 | \|X\| + \|Y\| |
| L<sub>X</sub> - L<sub>Y</sub> - L' - X - Y - R' | rotate L<sub>X</sub> - L<sub>Y</sub> - L' - X - Y to X - Y - L<sub>X</sub> - L<sub>Y</sub> - L'  | \|X\| + \|Y\| + (\|L\| - \|X\| - \|Y\|) + \|X\| + \|Y\| | \|X\| + \|Y\| | \|L\| |
| X - Y - L<sub>X</sub> - L<sub>Y</sub> - L' - R' | = reconfiguration 5 | | total = | \|L\| + \|X\| + \|Y\| |

- eliminates M
- works for all |L|
- same steps and effort as C1

Method D2:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L<sub>X</sub> - L<sub>Y</sub> - L' - Y - X - R' | rotate L<sub>X</sub> - L<sub>Y</sub> - L' - Y to Y - L<sub>X</sub> - L<sub>Y</sub> - L' | \|X\| + \|Y\| + (\|L\| - \|X\| - \|Y\|) + \|Y\| | 0 | \|L\| + \|Y\| |
| Y - L<sub>X</sub> - L<sub>Y</sub> - L' - X - R' | rotate Y - L<sub>X</sub> - L<sub>Y</sub> - L' - X to X - Y - L<sub>X</sub> - L<sub>Y</sub> - L'  | \|Y\| + \|X\| + \|Y\| + (\|L\| - \|X\| - \|Y\|) + \|X\| | \|X\| + \|Y\| | \|L\| |
| X - Y - L<sub>X</sub> - L<sub>Y</sub> - L' - R' | = reconfiguration 5 | | total = | 2\|L\| + \|Y\| |

- fewer moves than Method D1 if:
	- 2|L| + |Y| < |L| + |X| + |Y|
	- 2|L| < |L| + |X|
	- |L| < |X|
- works for all |L|
- same steps as C2

Method D3:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L<sub>X</sub> - L<sub>Y</sub> - L' - Y - X - R' | rotate Y - X to X - Y | \|X\| + \|Y\| | 0 | \|X\| + \|Y\| |
| L<sub>X</sub> - L<sub>Y</sub> - L' - X - Y - R' | swap L<sub>X</sub> - L<sub>Y</sub> with X - Y | 2\|X\| + 2\|Y\| | \|X\| + \|Y\| | \|X\| + \|Y\| |
| X - Y - L' - L<sub>X</sub> - L<sub>Y</sub> - R' | = reconfiguration 7 | | total = | 2\|X\| + 2\|Y\| |

- requires |L| >= |X| + |Y|
- same steps as C3, with one call eliminated due to |Z| == 0
- fewer moves than Method C1 if:
	- 2|X| + 2|Y| < |L| + |X| + |Y|
	- |X| + |Y| < |L|
	- |L| > |X| + |Y|
- fewer moves than Method C2 if:
	- 2|X| + 2|Y| < 2|L| + |Y|
	- 3|X| + |Y| < 2|L|
	- 1.5|X| + |Y| < |L|
	- |L| > 1.5|X| + |Y|

Algorithm D:

```
find X in R where X[i] < M[0]
if |X| == |R|:
	if |L| < |R|:
		Method B1
	else:
		Method B2
	merge completed
else:
	find Y in M where Y[i] < R'[0]
	if |Y| == |M|:
		find Z in L where Z[i] < R'[0]
		if |Z| == 0:
			if |L| < |X|:
				Method D2
			elif |L| < |X| + |Y|:
				Method D1
			else:
				Method D3
		else:
			if |L| < |X|:
				Method C2
			elif |L| < 2|X| + 2|Y| + |Z|
				Method C1
			else:
				Method C3
	else:
		if |L| < |X|:
			Method A3
		else if |L| < |M| + 2|X| + |Y|:
			Method A2
		else:
			Method A1
```

We should look at how we deal with the situation where |M| == 0.
This is the initial situation, and will occur at times throughout the algorithm.


Starting with an empty M:

| S | L | M | R |
|---|---|---|---|
| S | Z - L<sub>X</sub> - L' |  | X - R' |

we want to end up with X and Z appended to S, and our invariants kept: each of L, M, and R ordered internally and M < L.  There are 2 reconfigurations that give this:

Configuration 8:

| S | L | M | R |
|---|---|---|---|
| S - X - Z | L<sub>X</sub> - L' |  | R' |

- keeps empty M

Configuration 9:

| S | L | M | R |
|---|---|---|---|
| S - X - Z | L' | L<sub>X</sub> | R' |

- does not move L'

Method E1:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| Z - L<sub>X</sub> - L' - X - R' | rotate Z - L<sub>X</sub> - L' - X to X - Z - L<sub>X</sub> - L' | \|L\| + \|X\| | \|X\| + \|Z\| | \|L\| - \|Z\| |
| X - Z - L<sub>X</sub> - L' - R' | = reconfiguration 8 | | total = | \|L\| - \|Z\| |

- works for all |L|
- keeps M empty

Method E2:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| Z - L<sub>X</sub> - L' - X - R' | swap L<sub>X</sub> with X | 2\|X\| | 0 | 2\|X\| |
| Z - X - L' - L<sub>X</sub> - R' | rotate Z - X to X - Z | \|Z\| + \|X\| | \|Z\| + \|X\| | 0 |
| X - Z - L' - L<sub>X</sub> - R' | = reconfiguration 9 | | total = | 2\|X\| |

- works when |L| >= |X| + |Z|
- fewer moves than Method E2 when 2|X| < |L| - |Z|

Algorithm E:

```
loop:
	find X in R where X[i] < L[0]
	find Z in L where Z[i] < R'[0]
	if |L| < 2|X| + |Z|:
		Method E1
	else:
		Method E2
		while |M| > 0:
			find X in R where X[i] < M[0]
			if |X| == |R|:
				if |L| < |R|:
					Method B1
				else:
					Method B2
				merge completed
			else:
				find Y in M where Y[i] < R'[0]
				if |Y| == |M|:
					find Z in L where Z[i] < R'[0]
					if |Z| == 0:
						if |L| < |X|:
							Method D2
						elif |L| < |X| + |Y|:
							Method D1
						else:
							Method D3
					else:
						if |L| < |X|:
							Method C2
						elif |L| < 2|X| + 2|Y| + |Z|
							Method C1
						else:
							Method C3
				else:
					if |L| < |X|:
						Method A3
					else if |L| < |M| + 2|X| + |Y|:
						Method A2
					else:
						Method A1
```

Special case for |M| == 0:

If |X| == |R| (L<sub>0</sub> > R<sub>i</sub> for all i), then we simply need to reconfigure L - R to R - L as a final step to fully merged sequences.

Algorithm F:

```
loop:
	find X in R where X[i] < L[0]
	if |X| == |R|:
		rotate(L, R)
		merge completed
	else:
		find Z in L where Z[i] < R'[0]
		if |L| < 2|X| + |Z|:
			Method E1
		else:
			Method E2
			while |M| > 0:
				find X in R where X[i] < M[0]
				if |X| == |R|:
					if |L| < |R|:
						Method B1
					else:
						Method B2
					merge completed
				else:
					find Y in M where Y[i] < R'[0]
					if |Y| == |M|:
						find Z in L where Z[i] < R'[0]
						if |Z| == 0:
							if |L| < |X|:
								Method D2
							elif |L| < |X| + |Y|:
								Method D1
							else:
								Method D3
						else:
							if |L| < |X|:
								Method C2
							elif |L| < 2|X| + 2|Y| + |Z|
								Method C1
							else:
								Method C3
					else:
						if |L| < |X|:
							Method A3
						else if |L| < |M| + 2|X| + |Y|:
							Method A2
						else:
							Method A1
```

Note that Methods A3, B1, C2, and D1, are all triggered when |L| < |X|.
All methods also involve a rotation of M back into L.

Since we can check |L| < |X| before we find Y in M, we can perform this initial rotation early.
This allows us to search M-L as a single operation, rather than searching M and then L.

However, using the current algorithm, this may mean we find X in R as part of the |M| > 0 loop
and then search for it again when we drop back into the main loop.
To avoid, this we can make knowledge of X an invariant, moving it around to ensure it is known at the start of each loop.

Algorithm G:

```
find X in R where X[i] < L[0]
loop:
	assert |M| == 0
	if |X| == |R|:
		rotate(L, R)
		merge completed
	else:
		find Z in L where Z[i] < R'[0]
		if |L| < 2|X| + |Z|:
			Method E1
			find X in R where X[i] < L[0]
		else:
			Method E2
			find X in R where X[i] < M[0]
			loop:
				assert |M| > 0:
				if |L| < |X|:
					rotate(L, M)
					# merge M-L to L, and X still valid
					break
				else if |X| == |R|:
					Method B2
					merge completed
				else:
					find Y in M where Y[i] < R'[0]
					if |Y| == |M|:
						find Z in L where Z[i] < R'[0]
						if |Z| == 0:
							if |L| < |X| + |Y|:
								Method D1
								# Method D1 eliminates M
								find X in R where X[i] < L[0]
								break
							else:
								Method D3
						else:
							if |L| < 2|X| + 2|Y| + |Z|
								Method C1
								# Method C1 eliminates M
								find X in R where X[i] < L[0]
								break
							else:
								Method C3
					else:
						if |L| < |M| + 2|X| + |Y|:
							Method A2
						else:
							Method A1
					find X in R where X[i] < M[0]
```

Following implementation the following changes were made to the algorithm:

Since the Method D special case for |Z| == 0 is effectively covered by Method C, we can remove this case.
Tests show the effect on performance is minor, but removal makes the algorithm simpler.

Swaps are much cheaper than rotations, so rather than use the costs calculated above,
the algorithm uses the constraints on when particular methods are valid.

The algorithm as actually implemented is:

Algorithm H:

```
find X in R where X[i] < L[0]
loop:
	assert |M| == 0
	if |X| == |R|:
		rotate(L, R)
		merge completed
	else:
		find Z in L where Z[i] < R'[0]
		if |L| < |X| + |Z|:
			Method E1
			find X in R where X[i] < L[0]
		else:
			Method E2
			find X in R where X[i] < M[0]
			loop:
				assert |M| > 0:
				if |L| < |X|:
					rotate(L, M)
					# merge M-L to L, and X still valid
					break
				else if |X| == |R|:
					Method B2
					merge completed
				else:
					find Y in M where Y[i] < R'[0]
					if |Y| == |M|:
						find Z in L where Z[i] < R'[0]
						if |L| < |X| + |Y| + |Z|
							Method C1
							# Method C1 eliminates M
							find X in R where X[i] < L[0]
							break
						else:
							Method C3
					else:
						if |L| < |M| + |X|:
							Method A2
						else:
							Method A1
					find X in R where X[i] < M[0]
```

However, this algorithm has a problem.
Each time around the inner loop,
we move values from the front of R and the front of M,
opening up two gaps.

To fill the gap between L and M, we basically choose to shift L or M.

In typical mergesort, |L| and |R| start as n/2.
As we shift values out of L, M gets bigger.
At some point, L and M are (more or less) equal: |L| = |M| < n/4.
So worst case, we are shifting n/4 elements on each iteration.

Each iteration moves at least one value from M and one value from R, so there are n/2 iterations
(ignoring the setup stage and any patterns that eliminate M).
So, we're performing (n/2) x (n/4) = n<sup>2</sup>/8 shifts.
Hence, the merge is potentially O(n<sup>2</sup>).

To get a O(n log n) sort algorithm, the merge needs to be O(n).

So, back to the drawing board.

The problem is that low values are removed from both M and R, and, as this is done, two gaps are created.
The gap between M and R is OK, as we can extend M with values moved out of L.
Filling the gap between L and M is tricky.
Adding another sequence just adds more bookkeeping and propagates the problem.
Eventually, we need to remove an element from the front of this new sequence.

The alternative to creating new blocks in the gaps is to merge the new blocks immediately into a neighboring block.

For example, as soon as we create an M sequence, merge it into R.
If we insert M into R, then the highest value of M marks the start of the search for a new X.
(We know that M<sub>max</sub> < L<sub>0</sub> but we know nothing about R<sub>0</sub> in comparison to L).

This could be done as a recursive merge, using the algorithm we already have.  However, recursing would eliminate the O(1) memory use.

An alternative would be to merge based on insertion sort.
Insertion sort normally inserts unsorted data into a sorted sequence, but here we have an interesting property that the "unsorted" side is also sorted.

This additional knowledge allows us to change many of the single shifts into multiple shifts, and importantly, they are shifts into the final position.

For example, an algorithm for this insertion-merge could be:

- Find the insertion point pos1 in R for the largest M value first.

	`a c g [l] / b d e f h i j k (pos1) m`

- Find the insertion point pos0 for the next largest value in M.

	`a c [g] l / b d e f (pos0) h i j k (pos1) m`

- Swap M[max] with the value at R[pos0]. M now contains 2 values that go next to each other in the final sequence.

	`a c g [h] / b d e f (pos0) [l] i j k (pos1) m`

- Rotate the sequence in R from pos0 .. pos1 left one, so all R values shift left and the M value moves to the end.

	`a c g h / b d e f (pos0) i j k [l] (pos1) m`

- Set pos1 = pos0

	`a c g h / b d e f (pos1) i j k l m`

- Find the insertion point pos0 for the next largest value in M.

	`a [c] g h / b (pos0) d e f (pos1) i j k l m`

- Swap 2 values above pos0 with the highest 2 values in M. M now contains 3 values that go next to each other in the final sequence.

	`a c [d e] / b (pos0) [g h] f (pos1) i j k l m`

- Rotate the sequence in R from pos0 .. pos1 left 2, so all R values shift left and the M value moves to the end.

	`a [c] d e / b (pos0) f [g h] (pos1) i j k l m`

- Repeat, incrementing the number of values swapped each time, with an end-game for when either side does not have enough values.

> Alternatively, when we move R<sub>low</sub> to L<sub>low</sub> and open a gap in front of R, open a similar gap at end of R (called B) by moving R<sub>high</sub> values and inserting them into L<sub>high</sub>. Call the sorted L<sub>high</sub> block H.  Move L<sub>low</sub> into B backwards.
>
So, the gap at the front of R is filled with high values from R, and the gap at end of R is filled with low values from L. Note that |H| >= |B|.
>
When values from B need to be moved back to L, move elements from end of B to L, move elements from end of H to end of B and mark them sorted. Move elements from start of B to start of H and insert them into the end of L, expanding H. Finally move the elements taken from L at the beginning into the gap opened up at the start of B.
>
Note that this requires H to be shifted, and |H| >= |B|, and B is equivalent to M in Algorithm H.
So this would seem to perform more shifts than Algorithm H.

To make the insertion-merge algorithm more complete and general:

```
assert R[0] is lowest value
assert L[max] is highest value

- idx is the count of values in R known to be lower than L[0]
- pos is the insertion point of the value at R[idx] in L

idx = 1
while |L| > 1:
	idx = insertion point for L[0] in R[idx ..] + idx
	# now R[idx] = first R element with non-zero insertion point in L
	# This is almost the same as letting the main loop iterate through the
	# R values and finding the insertion point to be 0, except it avoids
	# calling lots of swaps and rotates for 0 (cheap, but not free) and it
	# allows galloping to kick in if there are many R values before L[0]
	if idx == |R|:
		# all values in R < all values in |L|
		break
	# we know R[idx] > L[0], so exclude it
	pos = insertion point for R[idx] in L[1 .. -1] + 1
	# now R[idx] < L[pos]
	if pos < idx:
		# move lowest values in R to leftmost position in L
		swap L[..pos] and R[..pos]
		# the new R[..pos] are > R[idx - 1] but < R[idx]
		rotate R[..idx], idx - pos
		# L[.. pos] are now the lowest values in correct position:
		# add them to sorted by trimming L
		L = L[pos..]
		# the values moved to R are still < R[idx] and in fact
		# R[idx] is the next lowest value and is less than L[0] (was L[pos])
		idx += 1
	else:
		# move the highest values in L[..pos] out of the way to allow us to
		# shift the lowest values from R to front of sequence.  Do this by
		# swapping the high L values and the low R values, then rotating the
		# low L values into their final position.
		swap L[pos - idx .. pos], R[.. idx]
		rotate L[.. pos], idx
		# L[.. pos] are now the lowest values in correct position:
		# add them to sorted by trimming L
		L = L[pos ..]
		# the highest values moved to R are still < R[idx] and in fact
		# R[idx] is the next lowest value and is less than L[0] (was L[pos])
		idx += 1
# if |L| == 1, all values in R < all values in |L| (just L[max])
# if idx == |R|, all values in R < all values in |L|
rotate [L,R], R
return
```

While both branches perform a swap and a rotate,
the second branch rotates elements into their final position,
while the first branch rotates just to keep the right hand side in order.
Hence, the first branch does more bookkeeping work while the second branch generates more final product.
As `idx` increases with each iteration, the first branch (`pos < idx`) branch becomes more likely as the algorithm proceeds.

So, reducing `idx` whenever productive and efficient seems to be a useful enhancement.

If `idx > |L|`, then the algorithm can swap `L` and `R[..|L|]`, placing `|L|` elements in their final
position, and reducing `idx` by `|L|`.

We can also consider using rotation for smaller values of `idx`, especially to benefit from the stack buffer.

In the following algorithm, we also move the common code outside the `if`.

Algorithm I:

```
assert R[0] is lowest value
assert L[max] is highest value

- idx is the count of values in R known to be lower than L[0]
- pos is the insertion point of the value at R[idx] in L

idx = 1
while |L| > 1:
	idx = insertion point for L[0] in R[idx ..] + idx
	# now R[idx] = first R element with non-zero insertion point in L
	# This is almost the same as letting the main loop iterate through the
	# R values and finding the insertion point to be 0, except it avoids
	# calling lots of swaps and rotates for 0 (cheap, but not free) and it
	# allows galloping to kick in if there are many R values before L[0]
	if idx == |R|:
		# all values in R < all values in |L|
		break
	if idx > some_size():
		rotate L and some_size() values of R
		# adjust the indexes tracking L and R
		idx -= some_size()
		# idx > 0, so invariant that R[0] is minimum still holds
	# we know R[idx] > L[0], so exclude it
	pos = insertion point for R[idx] in L[1 .. -1] + 1
	# now R[idx] < L[pos]
	if pos < idx:
		# move lowest values in R to leftmost position in L
		swap L[..pos] and R[..pos]
		# the new R[..pos] are > R[idx - 1] but < R[idx]
		rotate R[..idx], idx - pos
	else:
		# move the highest values in L[..pos] out of the way to allow us to
		# shift the lowest values from R to front of sequence.  Do this by
		# swapping the high L values and the low R values, then rotating the
		# low L values into their final position.
		swap L[pos - idx .. pos], R[.. idx]
		rotate L[.. pos], idx
	# L[.. pos] are now the lowest values in correct position:
	# add them to sorted by trimming L
	L = L[pos ..]
	# the highest values moved to R are still < R[idx] and in fact
	# R[idx] is the next lowest value and is less than L[0] (was L[pos])
	idx += 1
# if |L| == 1, all values in R < all values in |L| (just L[max])
# if idx == |R|, all values in R < all values in |L|
rotate [L,R], R
return
```

So, can we simplify further and just use insertion-merge as the merge step of our algorithm?

Applying insertion merge (Algorithm I) with no other merge was faster, possibly due to fewer moves.

The original suggestion to keep the original merge, but merge M and R immediately using insertion merge gives Algorithm J:

```
find X in R where X[i] < L[0]
loop:
	assert |M| == 0
	if |X| == |R|:
		rotate(L, R)
		merge completed
	else:
		find Z in L where Z[i] < R'[0]
		if |L| < |X| + |Z|:
			Method E1
			find X in R where X[i] < L[0]
		else:
			Method E2, creating M
            insertion_merge(M, R)
            find X in R where X[i] < L[0]
```

Algorithm J was faster than Algorithm I, possibly due to the smaller sizes of the merged sequences.

Given that M is being merged into R, we don't necessarily require that M is calculated the same way.
We can reduce the number of rotations by swapping X (the part of R that is less than L<sub>0</sub>) with L<sub>X</sub> without trying to find Z.

Algorithm K:

```
find X in R where X[i] < L[0]
loop:
	if |X| == |R|:
		rotate(L, R)
		merge completed
	else:
		if |L| < |X|:
			find Z in L where Z[i] < R'[0]
			rotate(Z-L'-X, X-Z-L')
			find X in R where X[i] < L[0]
		else:
			M = L[..|X|]
			swap(M, X)
            insertion_merge(M, R)
            find X in R where X[i] < L[0]
```

Whenever a value in M or R is shifted during the insertion merge, it's final position is known, and its next move will be to that position.
Hence, each element in L gets shifted 3 times (once as part of M moving to front of R, once during merge into R, and once to final position).
Each element in R gets shifted 2 times (once during merge with M, and once to final position).
Although, note, there are additional moves within the insertion merge.

A potential problem with this algorithm is that if M<sub>max</sub> == L'<sub>0</sub>, they get split and M<sub>max</sub> gets merged into R.
Any stable comparison of this M<sub>max</sub> value with L<sub>0</sub> will then get ordered incorrectly.
This isn't actually a problem as we know that all values in R < M<sub>max</sub> are less than L.
We should probably express the last two algorithms as inserting R into M, to create M < L<sub>0</sub> and R > L<sub>0</sub>.

Algorithm K was slightly faster on random data than Algorithm J, but significantly slower on data containing a pattern (e.g. ascending and descending).
The timings for these moved closer to the standard library sort.
If Algorithm K was written before Algorithm J, J would be considered a major improvement in sort times for pattern-containing data with neglible cost to random data.
Hence, we abandon K for the moment.

One tentative conclusion of J vs K is that performing a galloping search along *both* sequences helps to speed up sequences containing patterns, and has low cost on random sequences.

With random data, the algorithm is likely to find that X and Z are often very small. When we perform Method E2 to create M, it may often contain one element. When we perform Method E2 to create M of size 1, we then shift all values in R < M left one, and then in the subsequent step move those values to L. Since |M| = 1 is likely to be common in random data, this causes a lot of single shifting of R.  We can short-cut this step by swapping all values of R < M into L to create a larger M.  A larger M allows us to shift more of R further on each iteration.

Starting with |M| = 1, and X contains all values of R less than M<sub>0</sub>.

| S | L | M | R |
|---|---|---|---|
| S | L | M | X - R' |

we want to end up with X appended to S, and our invariants kept: each of L, M, and R ordered internally and M < L:

Configuration 10:

| S | L | M | R |
|---|---|---|---|
| S - X | L' | M - L<sub>X</sub> | R' |

Method F1:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| Z - L<sub>X</sub> - L' - M - X - R' | swap L<sub>X</sub> with X | 2\|X\| | \|X\| | \|X\| |
| Z - X - L' - M - L<sub>X</sub> - R' | = reconfiguration 10 | | total = | \|X\| |

- only works for |X| <= |L|
- note, if |L| == |X|, we can forget L and rename M as L
- if |L| < |X|, we can swap |L| values, forget L, and rename M as L, but we also know that the remainder of X < L - this can be handled as a rotation of L' - M - X. M < R, so M can be appended to R.

Method F2:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| L - M - X - R' | rotate L - M - X to X - L - M | \|L\| + \|X\| + 1 | \|X\| | \|L\| + 1 |
| X - L - M - R | merge M to R | | total = | \|L\| + 1 |

- fewer moves when \|L\| + 1 < \|X\|

This was implemented as Algorithm L. It has minimal effect on timings.

To avoid rotates, try doing swaps of equal size.

| S |     L     |    R    |
|---|-----------|---------|
|   | 1 3 5 7 9 | 2 4 6 8 |

First, trim left and right sides

| S |      L      |   R   |
|---|-------------|-------|
| 1 | 3 5 7 9 | 2 4 6 8 |

Then search for insertion point of L<sub>0</sub> in R.

| S |      L      |   R   |
|---|-------------|-------|
| 1 | 3 5 7 9 | 2 / 4 6 8 |

Then swap the lower values from R with an equal block in L, moving the R blocks into S.

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 | 5 7 9 | 3 / 4 6 8 |

Then merge the swapped L block into R. Note, this is recursive here. Keep a high-water mark for where the merge moves the highest value of L.

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 | 5 7 9 11 | 3 / 4 6 8 10 |

Repeat.

Search for insertion point of L<sub>0</sub> in R, using high-water mark to start search.

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 | 5 7 9 11 | 3 4 / 6 8 10 |

Then swap the lower values from R with an equal block in L, moving the R blocks into S.

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 3 4 | 9 11 | 5 7 / 6 8 10 |

Then merge the swapped L block into R

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 3 4 | 9 11 | 5 6 7 / 8 10 |

When |L| < |X|, use rotation, and then reset L and R.

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 3 4 5 6 7 | 9 11 | 8 10 |

Search for insertion point of L<sub>0</sub> in R, using high-water mark to start search.

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 3 4 5 6 7 | 9 11 | 8 / 10 |

Then swap the lower values from R with an equal block in L, moving the R blocks into S.

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 3 4 5 6 7 8 | 11 | 9 / 10 |

Then merge the swapped L block into R

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 3 4 5 6 7 8 | 11 | 9 / 10 |

Search for insertion point of L<sub>0</sub> in R, using high-water mark to start search.

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 3 4 5 6 7 8 | 11 | 9 10 / |

When |L| < |X|, use rotation, and then reset L and R.

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 3 4 5 6 7 8 9 10 | 11 | |

Terminate when L or R is empty.

This has a dysfunctional form when L is mostly sorted:

| S |      L      |   R   |
|---|-------------|-------|
|   | 2 3 4 5 6 10 | 1 7 8 9 |

First, trim left and right sides

| S |      L      |   R   |
|---|-------------|-------|
|   | 2 3 4 5 6 10 | 1 7 8 9 |

Then search for insertion point of L<sub>0</sub> in R.

| S |      L      |   R   |
|---|-------------|-------|
|   | 2 3 4 5 6 10 | 1 / 7 8 9 |

Then swap the lower values from R with an equal block in L, moving the R blocks into S.

| S |      L      |   R   |
|---|-------------|-------|
| 1 | 3 4 5 6 10 | 2 / 7 8 9 |

Then merge the swapped L block into R

| S |      L      |   R   |
|---|-------------|-------|
| 1 | 3 4 5 6 10 | 2 7 8 9 |

Then search for insertion point of L<sub>0</sub> in R.

| S |      L      |   R   |
|---|-------------|-------|
| 1 | 3 4 5 6 10 | 2 / 7 8 9 |

Then swap the lower values from R with an equal block in L, moving the R blocks into S.

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 | 4 5 6 10 | 3 / 7 8 9 |

This continues, with each single value being bounced up into R, and then down into S.

This can also occur with larger subsequences, e.g.

| S |      L      |   R   |
|---|-------------|-------|
|   | 3 4 5 6 7 10 | 1 2 / 8 9 |

In this case, we want to rotate the block to put the low L values in place.
We can do this by looking for R'[0] in L

Algorithm M:

```
hw = 1
while |L| > 1 and |R| > 1:
	find X in R[hw..] where X[i] < L[0]
	if |X| == |R|:
		rotate(L, R)
		return # merge completed
	find Z in L where Z[i] <= R'[0]
	if |L| <= |X|:
		# l0,l1,...,lz,(rx+1),lz+1,...,l|L| / r0,r1,...,rx,(l0),rx+1,...,r|R|
		rotate L-X by |X|
		# r0,r1,...,rx,l0,l1,...,lz,(rx+1),lz+1,...,l|L| / rx+1,...,r|R|
		add |X| + |Z| elements to S # l0+=|X|+|Z|, r0+=|X|
		# (rx+1),lz+1,...,l|L| / rx+1,...,r|R|
		# R[0] < L[0]
		hw = 1
	elif |Z| < |X|:
		# l0,l1,...,lz,(rx+1),lz+1,...,lx,lx+1,...,l|L| / r0,r1,...,rx,(l0),rx+1,...,r|R|
		swap |X| elements from L with X
		# r0,r1,...,rx,(l0),lx+1,...,l|L| / l0,l1,...,lz,(rx+1),lz+1,...,lx,rx+1,...,r|R|
		add |X| elements to S # l0+=|X|
		# lx+1,...,l|L| / l0,l1,...,lz,(rx+1),lz+1,...,lx,rx+1,...,r|R|
		# first |Z| elements of X' < rx+1
		hw = find lx in rx+1..r|R|
		# lx+1,...,l|L| / l0,l1,...,lz,(rx+1),lz+1,...,lx,rx+1,,...,ry,(lx),ry+1,...,r|R|
		merge_trimmed(lz+1..ry)
	else:
		# l0,l1,...,lx,lx+1,...,lz,(rx+1),lz+1,...,l|L| / r0,r1,...,rx,(l0),rx+1,...,r|R|
		swap |X| elements from RHS of Z with X
		# l0,l1,...,lx,r0,r1,...,rx,(l0),lz+1,...,l|L| / lx+1,...,lz,rx+1,...,r|R|
		rotate Z by |Z| - |X|
		# r0,r1,...,rx,l0,l1,...,lx,lz+1,...,l|L| / lx+1,...,lz,rx+1,...,r|R|
		add |Z| elements to S # l0+=|Z|
		# lz+1,...,l|L| / lx+1,...,lz,rx+1,...,r|R|
		# R already in order and we know rx+1 < lz+1
		hw = |X| + 1
rotate(L, R)
```

This is a relatively big improvement in sort times.
Note that it follows the same structure as Algorithm I - the insertion-merge algorithm.
However, it always moves the maximum of \|X\| or \|Z\| items into place rather than just the \|Z\| items for Algorithm I.
On the other hand, being recursive, this algorithm does not have O(1) memory usage.

We can add Algorithm I (rewritten to demonstrate its similarity) as a terminating step to re-create Algorithm J.
Since Algorithm M is faster than Algorithm I, we make the level of recursion a parameter. Setting it to 1 gives Algorithm J, which uses Algorithm M calling Algorithm I for merging. Setting it to 0 just gives Algorithm I, and setting it higher gives multiple levels of Algorithm M before Algorithm I is used.

Testing shows that the timings improve with more levels of Algorithm M.

From the original algorithms, we can also see that L can be rotated when \|L\| < \|X\| + \|Z\|, which keeps the algorithm out of \|Z\| < \|X\| section more often.
