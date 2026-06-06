# trailing_zeros_u64

Minimal single-`while`-loop reference: count the trailing zero bits of a
`u64` by shift-and-count.

`trailing_zeros_u64(x)` returns the number of low-order zero bits of `x`,
with `trailing_zeros_u64(0) == 64`.

## Contract

- `trailing_zeros_u64(0) == 64`.
- For `x != 0`, let `r = trailing_zeros_u64(x)`:
  - `r < 64`;
  - `2^r` divides `x`;
  - bit `r` of `x` is set (`(x >> r) & 1 == 1`), so `r` is the position of
    the lowest set bit and `x` is not divisible by `2^(r + 1)`.

## Why it exists

It is the helper shape Stein's binary GCD depends on: a single `while`
loop whose termination measure is the working value walked down bit by
bit (it halves each iteration). The loop uses only `==`, `&`, `>>`, `+`,
all of which the Hax Lean prelude models.
