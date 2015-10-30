# insort

A repository to keep some experiments with insertion sort on Agda.

| File              | Description                                                                               |
|-------------------|-------------------------------------------------------------------------------------------|
| Nat.agda          | a minimal file with naturals and comparisons                                              |
| NatPrime.agda | a minimal file with naturals and comparisons and nice min function
| Eq.agda           | a minimal file with equalities and properties                                             |
| Sort.agda         | insertion sort of nats with lists and vectors and oredered lists                          |
| SortLive.agda | version of Sort.agda done live in the tutorial and using the nicer min from NatPrime.agda|
| MSort.agda        | Sort of vectors with modules instead of nats                                              |
| NatSort.agda      | Sorting vectors of nats using MSort                                                       |
| NonEmptySort.agda | Sorting non-empty ordered vectors                                                         |
| ExSort.agda       | Proof that insertion sort on lists produces oredered lists and preserves length           |
| ExSortSimple.agda | Same as ExSort.agda with slightly simpler definition (but less general) of oredered lists |
