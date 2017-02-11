# gidsort
Non-allocating in-place mergesort

Mergesort is a very pleasant sorting algorithm, providing a stable sort with O(n log n) performance if we allow O(n) memory usage.

For very large n, we'd prefer to have something less than O(n) memory use.
Ideally, we'd get O(1) memory usage while keeping the stability and O(n log n) performance.
O(1) means the algorithm uses a fixed amount of memory (variables and stack) independent of the size of the structure to be sorted.
Sorts with O(1) memory use are called in-place sorts.

Most attempts to create an in-place mergesort either lose the property of stability, fail to sort for some patterns, or reach a point where the constants for the complexity values are too high to be practical.

A common pattern for in-place mergesorts is to break the structure into √n sized blocks and move the highest values to one end to create a workspace with which to perform a standard merge on each block.

The algorithm here avoids that approach, and starts with the observation that for a merge of two structures L = {l<sub>0</sub>...l<sub>|L|</sub>} and R = {r<sub>0</sub>...r<sub>|R|</sub>}:

| S |      L      |   R   |
|---|-------------|-------|
|   | 1 2 3 7 8 9 | 4 5 6 |

the first value in the sorted sequence is either l<sub>0</sub> or r<sub>0</sub>.  While it is l<sub>0</sub> we can simply change our boundaries to indicate that the sequence is sorted:

| S |      L      |   R   |
|---|-------------|-------|
| 1 2 3 | 7 8 9 | 4 5 6 |

When the lowest value is r<sub>0</sub>, we must move r<sub>0</sub> to the location occupied by l<sub>0</sub>. The simplest way to do that is to swap l<sub>0</sub> and r<sub>0</sub>.

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

If M+L or R become empty, the sort is finished.

Works great! And it took only 6 comparisons and 3 swaps to sort 9 values. Nice!

Except this particular sequence had no point where M<sub>0</sub> held the lowest unsorted value.

That's where it gets tricky.

