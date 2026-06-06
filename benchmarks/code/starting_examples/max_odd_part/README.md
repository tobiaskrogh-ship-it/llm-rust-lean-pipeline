# max_odd_part

Reference example for **an outer `while` loop whose body calls a looping
helper function** — the proof shape Stein's binary GCD needs.

`max_odd_part(n)` is the largest "odd part" among the integers `1..=n`,
where the odd part of `i` is `i` with all factors of two removed
(`i >> trailing_zeros_u64(i)`). `max_odd_part(0) == 0`.

## Structure

- `trailing_zeros_u64` — a private helper containing a single `while`
  loop (the shift-and-count pattern; see the `trailing_zeros_u64`
  reference crate).
- `max_odd_part` — the public target: a counter `while` loop over
  `1..=n` whose body **calls `trailing_zeros_u64`**.

Verifying `max_odd_part` requires proving the helper's postcondition and
then **composing** it into the outer loop's body step (the helper call
appears as a `let r ← trailing_zeros_u64 i` bind that must be inverted).
This is the same composition Stein's binary GCD needs for
`m >>= trailing_zeros_u64(m)`.

## Contract

- `max_odd_part(n) <= n` for every `n`.
- `max_odd_part(n)` is odd whenever `n >= 1`.
