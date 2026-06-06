-- Companion obligations file for the `clever_106_even_odd_palindrome` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_106_even_odd_palindrome

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_106_even_odd_palindromeObligations

/-! ## Nat-level oracle for the contract

`rev_at_nat` mirrors the Rust `rev_at` recursion at the `Nat` level
without any overflow concerns; the Rust function and this spec agree
exactly when `rev_at` does not overflow.

`is_palindrome_nat` is the Boolean palindrome predicate via digit
reversal — defined directly on `Nat` rather than `u64`.

`count_pal n p` is the prefix-scan oracle counting `k ∈ [1, n]` whose
remainder modulo 2 equals `p` and which are palindromes. -/

/-- Reverse the base-10 digits of `n` into accumulator `acc`, on `Nat`. -/
private def rev_at_nat (n acc : Nat) : Nat :=
  if h : 0 < n then rev_at_nat (n / 10) (acc * 10 + n % 10)
  else acc
termination_by n
decreasing_by exact Nat.div_lt_self h (by decide)

/-- Boolean palindrome test on `Nat` via digit reversal. -/
private def is_palindrome_nat (n : Nat) : Bool := rev_at_nat n 0 == n

/-- Count of palindromes in `[1, n]` whose remainder modulo 2 equals
    `parity`. Structurally recursive on the first argument, so it
    descends `n → n−1 → … → 0` exactly mirroring the prefix-scan
    semantics of `count_at`. -/
private def count_pal : Nat → Nat → Nat
  | 0,     _      => 0
  | k + 1, parity =>
      count_pal k parity
        + (if is_palindrome_nat (k + 1) && (k + 1) % 2 == parity then 1 else 0)

/-! ## Contract clauses

The Rust source contains four contract-style tests in `mod tests`:

  * `known` — two unit pins: `even_odd_palindrome(3) = (1, 2)` and
    `even_odd_palindrome(12) = (4, 6)`.  One theorem each.
  * `empty_range_is_zero_zero` — boundary clause: `n = 0 → (0, 0)`.
  * `even_count_matches_spec` and `odd_count_matches_spec` —
    component-by-component postcondition against the prefix-scan
    oracle.  Stated separately so a component-swap bug is localised.

### Feasibility note on the main postconditions

The proptests bound `n ∈ 0u64..=500`, but the function is well-defined
on a wider range.  The only overflow site is `rev_at`'s
`acc *? 10 +? n %? 10` recursion, which fails when `reverse(k) ≥ 2^64`
— i.e., when `k` has 20 base-10 digits and its digit reversal exceeds
`u64::MAX`.  For `k < 10^19`, `k` has at most 19 digits and
`reverse(k) < 10^19 < 2^64 ≈ 1.844 · 10^19`.  Intermediate
accumulator values are prefixes of `reverse(k)` (each step is
`acc' = acc * 10 + digit ≤ reverse(k)`), so they fit too.  Hence the
universal Lean statement holds in `n.toNat < 10^19`; outside that
range, `rev_at` can overflow.

The ascending counter `k +? 1` is safe in the same range (the last
recursive call uses `k = n` and computes `n + 1 ≤ 10^19 < 2^64`).
The accumulator increments `e +? 1`, `o +? 1` are safe because
`e, o ≤ n < 10^19 < 2^64`. -/

/-- Boundary clause: `even_odd_palindrome 0 = (0, 0)`.  The half-open
    range `[1, 0]` is empty, so no palindromes are counted, regardless
    of parity.  Captures the property test `empty_range_is_zero_zero`. -/
theorem empty_range_is_zero_zero :
    clever_106_even_odd_palindrome.even_odd_palindrome 0
      = RustM.ok (rust_primitives.hax.Tuple2.mk (0 : u64) (0 : u64)) := by
  sorry

/-- Unit pin from `known`: `even_odd_palindrome 3 = (1, 2)`.
    Palindromes in `[1, 3]`: `{1, 2, 3}`.  Even: `{2}` ⇒ 1; odd:
    `{1, 3}` ⇒ 2.  Pins both the parity split and the inclusive upper
    bound `k = n`. -/
theorem even_odd_palindrome_at_3 :
    clever_106_even_odd_palindrome.even_odd_palindrome 3
      = RustM.ok (rust_primitives.hax.Tuple2.mk (1 : u64) (2 : u64)) := by
  sorry

/-- Unit pin from `known`: `even_odd_palindrome 12 = (4, 6)`.
    Palindromes in `[1, 12]`: `{1..9, 11}`.  10 is *not* a palindrome
    (its digit-reversal is `1`).  Even: `{2, 4, 6, 8}` ⇒ 4; odd:
    `{1, 3, 5, 7, 9, 11}` ⇒ 6.  Differentiates the two-digit case from
    the single-digit case and pins down that 10 ≠ 01 as integers. -/
theorem even_odd_palindrome_at_12 :
    clever_106_even_odd_palindrome.even_odd_palindrome 12
      = RustM.ok (rust_primitives.hax.Tuple2.mk (4 : u64) (6 : u64)) := by
  sorry

/-- Postcondition (component 0, even count): the first component of
    `even_odd_palindrome n` equals the number of even palindromes in
    `[1, n]` as defined by digit reversal on `Nat`.

    Captures the proptest `even_count_matches_spec`.  The precondition
    `n.toNat < 10 ^ 19` rules out the wrapping case where `rev_at`
    overflows on a 20-digit input (see the feasibility note); within
    that range the universal Lean statement holds. -/
theorem even_count_matches_spec
    (n : u64) (h_fit : n.toNat < 10 ^ 19) :
    ∃ e o : u64,
      clever_106_even_odd_palindrome.even_odd_palindrome n
        = RustM.ok (rust_primitives.hax.Tuple2.mk e o)
      ∧ e.toNat = count_pal n.toNat 0 := by
  sorry

/-- Postcondition (component 1, odd count): the second component of
    `even_odd_palindrome n` equals the number of odd palindromes in
    `[1, n]` as defined by digit reversal on `Nat`.

    Captures the proptest `odd_count_matches_spec`.  Stated separately
    from `even_count_matches_spec` so a component-swap bug — e.g. the
    implementation accidentally increments `e` on odd hits — surfaces
    as an independent failure. -/
theorem odd_count_matches_spec
    (n : u64) (h_fit : n.toNat < 10 ^ 19) :
    ∃ e o : u64,
      clever_106_even_odd_palindrome.even_odd_palindrome n
        = RustM.ok (rust_primitives.hax.Tuple2.mk e o)
      ∧ o.toNat = count_pal n.toNat 1 := by
  sorry

end Clever_106_even_odd_palindromeObligations
