# find_zero

## Signature

```rust
pub fn find_zero(xs: &[i64]) -> i64
```

## Docstring

xs are coefficients of a polynomial.
find_zero find x such that poly(x) = 0.
find_zero returns only only zero point, even if there are many.
Moreover, find_zero only takes list xs having even number of coefficients
and largest non zero coefficient as it guarantees a solution.
Note(George): This problem has been modified from the original HumanEval spec because of Real is not a computable type, but a zero does not necessarily exist over the rationals.

