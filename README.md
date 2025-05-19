# Substring Counting with Insertions

This is a C++ implementation of the algorithms presented in the paper: *Brank J., Hočevar T. "Substring Counting with Insertions".*

The main part is the function `Solve`, which accepts strings `s`, `t`, `p` and calculates, for each position $k$, where `t` may be inserted into `s`, the number of occurrences of `p` as a substring in the string `s[:k] t s[k:]`.

It incorporates algorithms of different time complexities, most notably a linear-time solution to the problem in $O(s+t+p)$.