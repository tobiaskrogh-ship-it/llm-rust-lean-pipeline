# next_smallest

## Signature

```rust
pub fn next_smallest(lst: &[i64]) -> Option<i64>
```

## Docstring

You are given a list of integers.
Write a function next_smallest() that returns the 2nd smallest element of the list.
Return None if there is no such element.
TODO(George): Remove this when being reviewed
The spec is defined as: if result is none there is no second smallest element, which
exists in a finite list iff there are at least two distinct elements in the list.
If result is some x, then x is the second smallest element of the list, the spec
obtains the sublist of elements smaller than the result, and checks that this
sublist does not contain two distinct elements (they are all the same).

