-- Companion obligations file for the `clever_050_monotonic` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_050_monotonic

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_050_monotonicObligations

/-! ## Specification: pairwise predicates on the underlying `i64` list. -/

/-- All adjacent pairs of `l` are non-decreasing. -/
private def is_nondec (l : RustSlice i64) : Prop :=
  ∀ j : Nat, ∀ (hj1 : j + 1 < l.val.size),
    l.val[j]'(Nat.lt_of_succ_lt hj1) ≤ l.val[j+1]'hj1

/-- All adjacent pairs of `l` are non-increasing. -/
private def is_noninc (l : RustSlice i64) : Prop :=
  ∀ j : Nat, ∀ (hj1 : j + 1 < l.val.size),
    l.val[j+1]'hj1 ≤ l.val[j]'(Nat.lt_of_succ_lt hj1)

/-! ## Numeric helpers -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl

private theorem u64_toUSize64_toNat (i : u64) : (UInt64.toUSize64 i).toNat = i.toNat := by
  show (USize64.ofNat i.toNat).toNat = i.toNat
  exact USize64.toNat_ofNat_of_lt' i.toNat_lt

private theorem usize_toUInt64_toNat_of_lt (x : usize) (h : x.toNat < 2^64) :
    (USize64.toUInt64 x).toNat = x.toNat := by
  show (Nat.toUInt64 x.toNat).toNat = x.toNat
  exact UInt64.toNat_ofNat_of_lt h

private theorem u64_add_one_toNat (i : u64) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h' : i.toNat + (1 : u64).toNat < 2^64 := by rw [u64_one_toNat]; exact h
  rw [UInt64.toNat_add_of_lt h', u64_one_toNat]

private theorem u64_add_one_no_bv (i : u64) (h : i.toNat + 1 < 2^64) :
    BitVec.uaddOverflow i.toBitVec (1 : u64).toBitVec = false := by
  generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : u64).toBitVec = bo
  cases bo with
  | false => rfl
  | true =>
    exfalso
    have h1 : UInt64.addOverflow i 1 = true := hbo
    rw [UInt64.addOverflow_iff] at h1
    rw [u64_one_toNat] at h1
    omega

/-- `(i +? 1 : RustM u64) = pure (i + 1)` when `i.toNat + 1 < 2^64`. -/
private theorem u64_add_one_pure (i : u64) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : u64) : RustM u64) = pure (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM u64) = pure (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : u64).toBitVec
        then (.fail .integerOverflow : RustM u64)
        else pure (i + 1)) = _
  rw [u64_add_one_no_bv i h]
  rfl

/-! ## Boundary clause: lists of length 0 or 1 are vacuously monotonic. -/

theorem monotonic_small_lists (l : RustSlice i64) (h : l.val.size ≤ 1) :
    clever_050_monotonic.monotonic l = RustM.ok true := by
  sorry

theorem monotonic_returns_true (l : RustSlice i64) (h : is_nondec l ∨ is_noninc l) :
    clever_050_monotonic.monotonic l = RustM.ok true := by
  sorry

theorem monotonic_returns_false (l : RustSlice i64)
    (h : ¬ is_nondec l ∧ ¬ is_noninc l) :
    clever_050_monotonic.monotonic l = RustM.ok false := by
  sorry

theorem monotonic_constant (l : RustSlice i64) (c : i64)
    (hconst : ∀ i : Nat, ∀ (hi : i < l.val.size), l.val[i]'hi = c) :
    clever_050_monotonic.monotonic l = RustM.ok true := by
  sorry

end Clever_050_monotonicObligations
