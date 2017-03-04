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
| X - Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L' - X - Y - R' | = reconfiguration 5 | | total = | \|L\| + \|X\| + \|Y\| - \|Z\| |

- eliminates M
- works for all |L|

Method C2:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| Z - L<sub>X</sub> - L<sub>Y</sub> - L' - Y - X - R' | rotate Z - L<sub>X</sub> - L<sub>Y</sub> - L' - Y to Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L' | \|Z\| + \|X\| + \|Y\| + (\|L\| - \|X\| - \|Y\| - \|Z\|) + \|Y\| | 0 | \|L\| + \|Y\| |
| Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L' - X - R' | rotate Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L' - X to X - Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L'  | \|Y\| + \|Z\| + \|X\| + \|Y\| + (\|L\| - \|X\| - \|Y\| - \|Z\|) + \|X\| | \|X\| + \|Y\| + \|Z\| | \|L\| - \|Z\| |
| X - Y - Z - L<sub>X</sub> - L<sub>Y</sub> - L' - R' | = reconfiguration 5 | | total = | 2\|L\| + \|Y\| - \|Z\| |

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

- requires |L| >= |X| + |Y|
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

One final special case, where |Z| == |L| (i.e. R'<sub>0</sub> > L<sub>i</sub> for all i).
We need to reconfigure Z - Y - X - R' to X - Y - Z - R' as a final step to fully merged sequences.

Method D1:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| Z - Y - X - R' | rotate Z - Y to Y - Z | \|Z\| + \|Y\| | 0 | \|Z\| + \|Y\| |
| Y - Z - X - R' | rotate Y - Z - X to X - Y - Z | \|Y\| + \|Z\| + \|X\| | \|Y\| + \|Z\| + \|X\| | 0 |
| X - Y - Z - R' | | | total = | \|Z\| + \|Y\| |

Method D2:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| Z - Y - X - R' | rotate Y - X to X - Y | \|Y\| + \|X\| | 0 | \|Y\| + \|X\| |
| Z - X - Y - R' | rotate Z - X - Y to X - Y - Z | \|Z\| + \|X\| + \|Y\| | \|Z\| + \|X\| + \|Y\| | 0 |
| X - Y - Z - R' | | | total = | \|Y\| + \|X\| |

- fewer moves than Method D1 if:
	- \|Y\| + \|X\| < \|Z\| + \|Y\|
	- \|X\| < \|Z\|

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
		if |Z| == |L|:
			if |X| < |Z|:
				Method D2
			else:
				Method D1
			merge completed
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
| Z - L<sub>X</sub> - L' - X - R' | rotate Z - L<sub>X</sub> - L' - X to X - Z - L<sub>X</sub> - L' - X | \|L\| + \|X\| | \|X\| + \|Z\| | \|L\| - \|Z\| |
| X - Z - L<sub>X</sub> - L' - R' | = reconfiguration 8 | | total = | \|L\| - \|Z\| |

- works for all |L|
- keeps M empty

Method E2:

| Sequence | Step | Total moves | Final moves | Net moves |
|---|---|---|---|---|
| Z - L<sub>X</sub> - L' - X - R' | swap L<sub>X</sub> with X | 2\|X\| | 0 | 2\|X\| |
| Z - X - L' - L<sub>X</sub> - R' | rotate Z - X to X - Z | \|Z\| + \|X\| | \|Z\| + \|X\| | 0 |
| X - Z - L' - L<sub>X</sub> - R' | = reconfiguration 9 | | total = | 2\|X\| |

- works when |L| >= |X|
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
					if |Z| == |L|:
						if |X| < |Z|:
							Method D2
						else:
							Method D1
						merge completed
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

Special cases for |M| == 0.

If |X| == |R| (L<sub>0</sub> > R<sub>i</sub> for all i), then we simply need to reconfigure L - R to R - L as a final step to fully merged sequences.

If |Z| == |L| (R'<sub>0</sub> > L<sub>i</sub> for all i), then we simply need to reconfigure Z - X to X - Z as a final step to fully merged sequences.

Algorithm F:

```
loop:
	find X in R where X[i] < L[0]
	if |X| == |R|:
		rotate(L, R)
		merge completed
	else:
		find Z in L where Z[i] < R'[0]
		if |Z| == |L|:
			rotate(Z, X)
			merge completed
		else if |L| < 2|X| + |Z|:
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
						if |Z| == |L|:
							if |X| < |Z|:
								Method D2
							else:
								Method D1
							merge completed
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
		if |Z| == |L|:
			rotate(Z, X)
			merge completed
		else if |L| < 2|X| + |Z|:
			Method E1
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
						if |Z| == |L|:
							Method D1
							merge completed
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
