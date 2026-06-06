-- Companion obligations file for the `is_multiple_of_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import is_multiple_of_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Is_multiple_of_u64Obligations

/-- Postcondition (b = 0 special case): when `b = 0`, the function returns
    `(a == 0)`. Captures the source's `if b == 0 { a == 0 } else …` branch
    and the boundary tests in `zero_divisor_only_zero`
    (`is_multiple_of(0, 0)` true; `is_multiple_of(1, 0)`, `(7, 0)`,
    `(u64::MAX, 0)` all false). -/
theorem is_multiple_of_zero_divisor (a : u64) :
    is_multiple_of_u64.is_multiple_of a 0 = RustM.ok (a == 0) := by
  -- The `b == 0` guard fires (with `b = 0`), the do-binds collapse on `pure`,
  -- and the body reduces to `pure (a == 0)` definitionally.
  rfl

/-- Postcondition (b ≠ 0 case): when `b ≠ 0`, the function returns
    `(a % b == 0)` — the standard divisibility check. Captures
    `agrees_with_division` (the exhaustive sweep for `a ∈ 0..=50`,
    `b ∈ 1..=20`), `known_values`, and the divisible cases of
    `large_values`. The `b ≠ 0` precondition guarantees the partial
    operation `%?` succeeds. -/
theorem is_multiple_of_nonzero_divisor (a b : u64) (h : b ≠ 0) :
    is_multiple_of_u64.is_multiple_of a b = RustM.ok (a % b == 0) := by
  -- Unfold the function and the two relevant operators (`==?` is `pure (· == ·)`,
  -- `%?` is `if y = 0 then .fail else pure (x % y)`). The `b == 0` guard is
  -- `false` because `h : b ≠ 0`, so the outer `if` selects the else-branch,
  -- and `if_neg h` collapses the `%?` to `pure (a % b)`.
  unfold is_multiple_of_u64.is_multiple_of
  simp only [rust_primitives.cmp.eq, rust_primitives.ops.arith.Rem.rem,
             pure_bind, if_neg h]
  -- Remaining: `if (b == 0) then RustM.ok (a == 0) else RustM.ok (a % b == 0)
  --              = RustM.ok (a % b == 0)`. The boolean is `false` since `b ≠ 0`.
  have hb_eq : (b == 0) = false := by
    rw [beq_eq_false_iff_ne]; exact h
  simp [hb_eq]
  -- `pure` for `RustM` is `RustM.ok`.
  rfl

/-- Postcondition (constructive direction, `b ≠ 0`): if there exists a
    Nat-witness `k` with `a.toNat = k * b.toNat` (i.e. `a` is a true
    integer multiple of `b`, with no `u64` overflow needed since the
    equation lives in `Nat`), then `is_multiple_of a b = true`.
    Captures `multiples_have_witnesses`, which constructs `a` from
    `k * b` rather than recomputing `a % b`. -/
theorem is_multiple_of_witness (a b : u64) (k : Nat) (h_b : b ≠ 0)
    (h_eq : a.toNat = k * b.toNat) :
    is_multiple_of_u64.is_multiple_of a b = RustM.ok true := by
  -- Step 1: dispatch via the b ≠ 0 postcondition.
  rw [is_multiple_of_nonzero_divisor a b h_b]
  -- Goal: `RustM.ok (a % b == 0) = RustM.ok true`, i.e. `(a % b == 0) = true`.
  -- Step 2: show `a % b = 0` at `Nat` level using `h_eq`, since `(k * n) % n = 0`.
  --   `Nat.mul_mod_right` is stated as `n * k % n = 0`, so commute first.
  have h_mod : (a % b).toNat = 0 := by
    rw [UInt64.toNat_mod, h_eq, Nat.mul_comm]
    exact Nat.mul_mod_right b.toNat k
  -- Step 3: lift `(a % b).toNat = 0` to `a % b = 0` via `toNat` injectivity.
  have h_amb : a % b = 0 := by
    apply UInt64.toNat.inj
    simpa using h_mod
  rw [h_amb]
  -- Goal: `RustM.ok ((0 : u64) == 0) = RustM.ok true`. The Bool literal reduces.
  rfl

/-- Postcondition (non-divisible direction, `b > 1`): if `a = q * b + r` in
    `Nat` with `0 < r < b`, then `is_multiple_of a b = false`. Captures
    `non_multiples_have_no_witness`, which constructs explicit non-multiples
    to rule out a buggy implementation that always returns `true`. -/
theorem is_multiple_of_non_witness (a b : u64) (q r : Nat)
    (h_b : 1 < b) (h_r_pos : 0 < r) (h_r_lt : r < b.toNat)
    (h_eq : a.toNat = q * b.toNat + r) :
    is_multiple_of_u64.is_multiple_of a b = RustM.ok false := by
  -- Step 1: derive `b ≠ 0` from `1 < b`.
  have h_b_ne : b ≠ 0 := by
    intro hb; subst hb
    -- `1 < (0 : u64)` is impossible.
    exact absurd h_b (by decide)
  -- Step 2: dispatch via the b ≠ 0 postcondition.
  rw [is_multiple_of_nonzero_divisor a b h_b_ne]
  -- Goal: `RustM.ok (a % b == 0) = RustM.ok false`, i.e. `(a % b == 0) = false`.
  -- Step 3: at the Nat level, `(a % b).toNat = r` because
  --   (q * b.toNat + r) % b.toNat = (r + q * b.toNat) % b.toNat
  --                                = r % b.toNat = r  (since r < b.toNat).
  have h_mod : (a % b).toNat = r := by
    rw [UInt64.toNat_mod, h_eq, Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt h_r_lt
  -- Step 4: `a % b ≠ 0` since `(a % b).toNat = r > 0`.
  have h_amb_ne : a % b ≠ 0 := by
    intro h
    rw [h] at h_mod
    -- `(0 : u64).toNat = 0`, contradicts `r > 0`.
    simp at h_mod; omega
  -- Step 5: turn `a % b ≠ 0` into `(a % b == 0) = false` and rewrite.
  have hbeq : (a % b == 0) = false := by
    rw [beq_eq_false_iff_ne]; exact h_amb_ne
  rw [hbeq]

/-- Totality / no-panic: the function returns a value for every pair of
    `u64` inputs. The `b == 0` guard short-circuits before `%?` is invoked,
    so the only partial operation in the body never fires on its failing
    input. This is the explicit "no failure mode" clause of the contract. -/
theorem is_multiple_of_total (a b : u64) :
    ∃ v : Bool, is_multiple_of_u64.is_multiple_of a b = pure v := by
  by_cases h : b = 0
  · subst h
    exact ⟨a == 0, is_multiple_of_zero_divisor a⟩
  · exact ⟨a % b == 0, is_multiple_of_nonzero_divisor a b h⟩

end Is_multiple_of_u64Obligations
