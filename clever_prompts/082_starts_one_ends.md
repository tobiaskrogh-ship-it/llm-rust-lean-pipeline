# starts_one_ends

## Signature

```rust
pub fn starts_one_ends(n: u64) -> u64
```

## Docstring

Given a positive integer n, return the count of the numbers of n-digit
positive integers that start or end with 1.
Note: For reviewer, I believe this is the most straightforward spec, and I am relying on Set cardianlity not being computable in general. The point of this problem is really to privide a formula.
Note: But I guess a program that goes through each number and adds 1 will be the same as a program that computes in O(1) under this view.

