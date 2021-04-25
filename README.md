# SortingAlgs

Final CS390 Project using the Idris language to implement and prove sorting algorithms

# Contents

We implemented provably correct implementations of quicksort, mergesort, and insertion sort in idris. we also implemented a permutation checker that given two lists, can determine if they are permutations of each other

# Development Notes

Developed and Tested on Idris v1.3.3

To run:

```
    idris sorting.idr -o sorting
    ./sorting
```

# References

-   [Ben Sherman Article](https://www.ben-sherman.net/posts/2014-09-20-quicksort-in-idris.html) on Quicksort in Idris
-   [Mergesort Implementation](https://github.com/Gwin73/idris-mergesort/blob/master/src/MergeSort.idr)
-   [Quicksort Implementation](https://gist.github.com/clayrat/ad916323a4e672c1d7dfa3a0ecf18d85#file-qsort-idr-L1)
-   [Edwin Brady](https://gist.github.com/edwinb/46da18e2fc6be3f92177ea02ea4b3a1a#file-mergesort-idr-L100) Mergesort Implementation
-   [Insertion Sort](https://github.com/davidfstr/idris-insertion-sort/blob/master/InsertionSort.idr) Example
-   Type-driven Development with Idris - Edwin Brady
