# Substring Counting with Insertions

This is a C++ implementation of the algorithms presented in the paper: *Brank J., Hočevar T. "Substring Counting with Insertions".*

The main part is the function `Solve`, which accepts strings `s`, `t`, `p` and calculates, for each position $k$, where `t` may be inserted into `s`, the number of occurrences of `p` as a substring in the string `s[:k] t s[k:]`.

It incorporates algorithms of different time complexities, most notably a linear-time solution to the problem in $O(s+t+p)$.

We list some important functions and data structures with brief descriptions. More detailed descriptions of functions and structures are available as comments in the source code. Individual steps of the algorithms are also thoroughly commented throughout the implementation.

- `Solve`: This function contains the main part of the solution of our problem. Given the strings `s`, `t`, `p`, its job is to calculate, for each position $k$ where `t` may be inserted into `s`, the number of occurrences of `p` as a substring in the string `s[:k] t s[k:]`. Which method is to be used to count those occurrences of `p` which begin within `s[:k]` and end within `s[k:]` is determined by the last argument of type `TMethod`, which can be `Quadratic`, `NSqrtN`, `NLogN`, `NearlyLinear`or `Linear`.

- `BuildSuffixTable`, `BuildSuffixTable2`, `BuildPrefixTable`, `BuildPrefixTable2` compute the prefix and suffix tables from the Knuth-Morris-Pratt algorithm that are used by all methods.

- `TKmpTree` is a tree data structure that represents the KMP tree. It is used in the `Quadratic`, `NSqrtN` and `NLogN` method to determine ancestors in the tree (shorter prefix-suffixes).

- `FenwickUpdate` and `FenwickQuery` implement the Fenwick tree data structure used by the `NLogN` method.

The `NearlyLinear` and `Linear` methods are the most complex and in addition rely on the following functions and structures.

- `BuildSuffixArray` builds the suffix array using the skew/DC3 algorithm and is optionally enhanced by the longest common prefix table built by the Kasai's algorithm (`BuildLcpArray`).

- `TSuffixTree` represents a suffix tree data structure that is built from the suffix array. It supports longest common prefix (LCP) queries for pairs of suffixes using the constant-time lowest common ancestor queries by Bender & Farach-Colton.

- `CountEarlyOccurrences`, `CountLateOccurrences` and `CountRemainingOccurrences` are components of the (nearly)linear algorithm and count occurrences of the pattern in the process of simplifying the search space.

- `TAncestorQueryProcessor` comes in a `_NearlyLinear` and `_Linear` version. They efficiently compute an entire batch of ancestor queries.
  - `TAncestorQueryProcessor_NearlyLinear` uses disjoint-set unions in the KMP tree.
  - `TAncestorQueryProcessor_Linear` improves this approach with a `TStaticTreeSetUnion` that implements a linear-time solution for the union-set problem in the special case where the elements are arranged in a tree and the union operation is always performed between the set containing an element and the set containing its parent (Gabow & Tarjan).

Most of the functions also come in a `_Naive` version, which are straight-forward but less efficient and were used to test the correctness of the implementation. Note that `Test*` functions typically compare the results of naive and more efficient versions.
