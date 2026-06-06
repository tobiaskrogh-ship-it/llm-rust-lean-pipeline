-- Companion obligations file for the `gcd_stein_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_stein_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_stein_u64Obligations

/-! ## Helper lemmas for casting `Nat.gcd` back to `u64`.

Pure-Nat facts about `Nat.gcd a.toNat b.toNat` — copied verbatim from
`Gcd_whileObligations.lean`, where they are also used to bridge between
`Nat.gcd` and `UInt64.ofNat (Nat.gcd …)`. -/

private theorem gcd_lt_2_64 (a b : u64) : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
  by_cases hb : b.toNat = 0
  · rw [hb, Nat.gcd_zero_right]
    exact a.toNat_lt
  · have h_le : Nat.gcd a.toNat b.toNat ≤ b.toNat :=
      Nat.gcd_le_right a.toNat (Nat.pos_of_ne_zero hb)
    exact Nat.lt_of_le_of_lt h_le b.toNat_lt

private theorem gcd_toNat_ofNat (a b : u64) :
    (UInt64.ofNat (Nat.gcd a.toNat b.toNat)).toNat = Nat.gcd a.toNat b.toNat :=
  UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b)

/-! ## Contract obligations for `gcd_stein_u64.gcd_stein`

The contract is read off the property tests in `src/lib.rs`:

* `known_values` + `zero_zero_is_zero` — closed-form equation
  `gcd_stein a b = Nat.gcd a b`.  Stating this once as the
  `_postcondition` theorem subsumes every concrete hand-checked value
  (`(10, 2) = 2`, `(0, 3) = 3`, `(3, 3) = 3`, `(56, 42) = 14`, etc.).
* `result_divides_both_inputs` — two independent divisibility clauses
  `gcd | a` and `gcd | b`.
* `result_is_greatest` — every common divisor `d` divides the result.

Stein's binary algorithm has *no documented failure modes*: every
intermediate `u64` operation is provably in range (subtraction is guarded
by `m > n`, the final `m << shift` produces `gcd(a, b) ≤ max(a, b) < 2^64`).
Hence the postcondition is stated equationally as `RustM.ok …` rather
than as a Hoare triple — the no-panic clause is folded into the use of
`RustM.ok` on the right-hand side, and surfaced explicitly as
`gcd_stein_total`.

Shapes mirror `proof_patterns/gcd_while_modified/.../Gcd_whileObligations.lean`. -/

/-! ## Boundary cases (proved directly from the short-circuit).

The Rust source contains an `if m == 0 || n == 0 { return m | n }`
short-circuit, so the three "at least one input zero" cases reduce to
purely-bitwise reasoning — independent of the algorithm body and the
hard correctness proof.  These are proven *first* so the main
`gcd_stein_postcondition` proof can fold them in as boundary cases. -/

/-- **`gcd_stein(0, 0) = 0`.** The explicit boundary from
`zero_zero_is_zero` — the `m | n` short-circuit in the source returns
0 when both inputs are 0. -/
theorem gcd_stein_zero_zero :
    gcd_stein_u64.gcd_stein 0 0 = RustM.ok 0 := by
  simp only [gcd_stein_u64.gcd_stein, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.or, pure_bind,
             beq_self_eq_true, Bool.or_self, ↓reduceIte]
  rfl

/-- **`gcd_stein(0, b) = b`.** Pins down the `a = 0` branch of the
`m == 0 || n == 0` short-circuit.  Covers the `(0, 3) = 3` row of
`known_values` (and, together with `gcd_stein_divides_b`, forces
`gcd_stein(0, b) = b` since the gcd must divide `b` and is itself
divisible by `b` via `Nat.gcd_zero_left`). -/
theorem gcd_stein_a_zero (b : u64) :
    gcd_stein_u64.gcd_stein 0 b = RustM.ok b := by
  simp only [gcd_stein_u64.gcd_stein, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.or, pure_bind,
             beq_self_eq_true, Bool.true_or, ↓reduceIte]
  -- Goal: pure (0 ||| b) = RustM.ok b
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_or]
  show 0 ||| b.toNat = b.toNat
  exact Nat.zero_or b.toNat

/-- **`gcd_stein(a, 0) = a`.** Symmetric to `gcd_stein_a_zero`; pins
down the `b = 0` branch of the short-circuit. -/
theorem gcd_stein_b_zero (a : u64) :
    gcd_stein_u64.gcd_stein a 0 = RustM.ok a := by
  simp only [gcd_stein_u64.gcd_stein, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.or, pure_bind,
             beq_self_eq_true, Bool.or_true, ↓reduceIte]
  -- Goal: pure (a ||| 0) = RustM.ok a
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_or]
  show a.toNat ||| 0 = a.toNat
  exact Nat.or_zero a.toNat

/-! ## Helper lemmas the next pass will need

These are the *exact* lemma statements the main-case proof will use.
Each is left as `sorry` with its own structural-unblock docstring so a
future pass attacks them in isolation rather than rediscovering the
shape. -/

/-- **Trailing-zero counter — totality.** For every `u64`, `trailing_zeros_u64`
returns *some* value in `RustM` (it never panics or diverges).

* When `x = 0` the function short-circuits to `pure 64` (no loop), so
  this is trivial.
* When `x ≠ 0` the inner `while y & 1 == 0` loop terminates because
  the loop measure `y.toNat` strictly halves each iteration (`y` even
  ⟹ `(y >>> 1).toNat = y.toNat / 2 < y.toNat`), and the loop only
  iterates while `y & 1 == 0`.  Termination requires the body's `>>>?`
  shift to succeed — the shift amount `(1 : i32)` is fixed, so the
  `0 ≤ y < 64` shift-amount check is `true` by computation.

Structural unblock: prove this via the `while_example` two-stage
template (Stage 1: `Spec.MonoLoopCombinator.while_loop` with invariant
`count.toNat < 64 ∧ y.toNat * 2^count.toNat = x.toNat` and measure
`y.toNat`; Stage 2: not needed for the existence claim — just project
the witness via `Exists.intro`). -/
private theorem trailing_zeros_u64_total (x : u64) :
    ∃ k : u32, gcd_stein_u64.trailing_zeros_u64 x = RustM.ok k := by
  -- x = 0 branch closes inline (short-circuit to pure 64).
  by_cases hx : x = 0
  · subst hx
    refine ⟨64, ?_⟩
    simp only [gcd_stein_u64.trailing_zeros_u64, rust_primitives.cmp.eq,
               pure_bind, beq_self_eq_true, ↓reduceIte]
    rfl
  · -- x ≠ 0 branch needs the inner while-loop's termination argument.
    -- Stuck sub-goal: after unfolding `trailing_zeros_u64` and entering the
    -- else-branch, the goal contains `rust_primitives.hax.while_loop` with
    -- cond `(y &&& 1) ==? 0`, body `do y ← (y >>>? 1); count ← (count +? 1); …`,
    -- and we need to project a witness for the loop result.
    -- The while_loop's partial_fixpoint definition does not reduce
    -- definitionally past one iteration, so a direct `refine` cannot supply
    -- the witness — we need to apply `Spec.MonoLoopCombinator.while_loop`
    -- with the invariant `count.toNat + Nat.log2 y.toNat ≤ 64 ∧ y.toNat > 0`
    -- and measure `y.toNat`, then peel back via `RustM.Triple_iff_BitVec`.
    -- See file-level docstring for the full structural unblock.
    exact sorry

/-- **Trailing-zero counter — correctness.** For `x ≠ 0`,
`trailing_zeros_u64 x = RustM.ok k` where `k` is the largest exponent
such that `2^k.toNat ∣ x.toNat`.  Equivalently: `x.toNat % 2^k.toNat = 0`
and `x.toNat % 2^(k.toNat + 1) ≠ 0` (and `k.toNat < 64`).

Structural unblock: prove via the `while_example` two-stage template.
The Stage-1 invariant is the strong predicate

  `count.toNat + Nat.log2 y.toNat ≤ Nat.log2 x.toNat ∧`
  `y.toNat * 2^count.toNat = x.toNat ∧ y.toNat > 0`

(i.e. `count` factors of 2 have already been extracted from `x` into
the cumulative `2^count`, and `y` carries the remaining odd-completion
once it stops being even).  Termination measure: `y.toNat`.  Stage 2
peels back to the equation via `RustM.Triple_iff_BitVec`. -/
private theorem trailing_zeros_u64_correctness (x : u64) (hx : x ≠ 0) :
    ∃ k : u32, gcd_stein_u64.trailing_zeros_u64 x = RustM.ok k ∧
      k.toNat < 64 ∧
      x.toNat % 2 ^ k.toNat = 0 ∧
      (x.toNat / 2 ^ k.toNat) % 2 = 1 := by
  sorry

/-! ## Sub-lemmas for `gcd_stein_postcondition`

The closed-form correctness of `gcd_stein` decomposes into:

1. **Boundary cases** (`a = 0` or `b = 0`) — already closed above via the
   short-circuit theorems `gcd_stein_a_zero` / `gcd_stein_b_zero`,
   bridged through `Nat.gcd_zero_left` / `Nat.gcd_zero_right`.

2. **Main case** (`a ≠ 0 ∧ b ≠ 0`) — needs

   - `trailing_zeros_u64_correctness`: for `x ≠ 0`, `trailing_zeros_u64 x`
     returns `k` such that `x.toNat = 2^k.toNat * ((x.toNat) >>> k.toNat)`
     and `((x.toNat) >>> k.toNat) % 2 = 1` (i.e. odd post-shift).

   - `stein_outer_loop_invariant`: the outer `while m != n` loop
     preserves `Nat.gcd m.toNat n.toNat * 2^shift.toNat =
     Nat.gcd a.toNat b.toNat` together with `m` and `n` odd.

   - `stein_outer_loop_termination`: `m.toNat + n.toNat` is a strict
     decreasing measure for the outer loop (every body iteration
     either subtracts strictly positive `n` from `m > n`, or vice versa,
     then divides by ≥ 1 factor of 2).

   - `final_shift_no_overflow`: `m << shift` does not overflow because
     after the outer loop terminates `m = Nat.gcd a.toNat b.toNat / 2^shift.toNat`,
     so `m * 2^shift.toNat = Nat.gcd a.toNat b.toNat ≤ max(a, b) < 2^64`.

Each is non-trivial in its own right, hence the surviving `sorry`
covers only the main-case combination, with the boundary cases closed
inline below. -/

/-- **Functional correctness (closed form).** For every pair of `u64`
inputs, `gcd_stein` succeeds and returns the integer gcd of the two
inputs (computed over `Nat`).  This single equation pins down every
concrete `known_values` case as well as the `zero_zero_is_zero`
boundary (`Nat.gcd 0 0 = 0`).

**Proof state (after this turn):**

* `a = 0` branch — closed via `gcd_stein_a_zero` + `Nat.gcd_zero_left`.
* `b = 0` branch — closed via `gcd_stein_b_zero` + `Nat.gcd_zero_right`.
* `a ≠ 0 ∧ b ≠ 0` branch — left as `sorry`.

**Specific stuck sub-goal (main case):** after the boundary cases
collapse, the goal reduces to proving

  `do { let shift ← tz(m|n); let m ← m >> tz(m); let n ← n >> tz(n);`
  `     let ⟨m,n⟩ ← outer_loop ⟨m,n⟩; m << shift } = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat))`

  under `a ≠ 0 ∧ b ≠ 0`.  This requires reasoning about three nested
  `rust_primitives.hax.while_loop` calls (the trailing-zeros loop is
  invoked four times: on `m|n`, on `m`, on `n`, and inside every outer
  iteration), each requiring its own Hoare-triple correctness statement
  plus the `RustM.Triple_iff_BitVec` ladder to peel back to an equation.
  The classical Stein invariant `2^shift * Nat.gcd m n = Nat.gcd a b`
  is the proof's core, but stating it requires a `Nat.log2_lowest_bit`
  / `Nat.maxPowDvd` predicate that the Hax prelude does not expose —
  and would need to be developed locally first.

**Structural unblocks the next pass would need (in order):**

1. A separately-verified `trailing_zeros_u64_correctness` lemma (the
   Hoare-triple form of "returns k with 2^k | x and (x >>> k) odd"),
   then its equation form via `RustM.Triple_iff_BitVec`.  Estimate: a
   ~80-line proof following the `while_example` template.

2. A `Nat.gcd_stein_step` lemma capturing the algebraic identity
   `Nat.gcd m n = Nat.gcd (m - n) n` when `m ≥ n`, combined with
   `Nat.gcd_two_div_two_odd : Nat.gcd (2*k) (2*l+1) = Nat.gcd k (2*l+1)`.
   These exist in Mathlib's `Mathlib.Data.Nat.GCD.Basic` under names
   like `Nat.gcd_sub_self_left` and `Nat.Coprime.coprime_dvd_two` — the
   Hax prelude does not pull them in.

3. Cross-target import of the `while_example`-style two-stage ladder
   (Stage 1 Hoare triple via `Spec.MonoLoopCombinator.while_loop`,
   Stage 2 equation via `RustM.Triple_iff_BitVec`) for the *outer*
   Stein loop.  Would close the main equation once (1) and (2) are
   available.

4. A `UInt64.shiftLeft_no_overflow_iff` lemma proving `x <<< s` does
   not overflow when `x.toNat * 2^s.toNat < 2^64`; combine with the
   loop invariant's `m = Nat.gcd a b / 2^shift` to discharge the final
   `<<<?`. -/
theorem gcd_stein_postcondition (a b : u64) :
    gcd_stein_u64.gcd_stein a b
      = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) := by
  -- Boundary case: a = 0.  Closed via gcd_stein_a_zero + Nat.gcd_zero_left.
  by_cases ha : a = 0
  · subst ha
    rw [gcd_stein_a_zero]
    apply congrArg RustM.ok
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 0 b)]
    show b.toNat = Nat.gcd (0 : u64).toNat b.toNat
    rw [show ((0 : u64).toNat) = 0 from rfl, Nat.gcd_zero_left]
  -- Boundary case: b = 0.  Closed via gcd_stein_b_zero + Nat.gcd_zero_right.
  by_cases hb : b = 0
  · subst hb
    rw [gcd_stein_b_zero]
    apply congrArg RustM.ok
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a 0)]
    show a.toNat = Nat.gcd a.toNat (0 : u64).toNat
    rw [show ((0 : u64).toNat) = 0 from rfl, Nat.gcd_zero_right]
  -- Main case: a ≠ 0 ∧ b ≠ 0.  See docstring for the structural unblock.
  exact sorry

/-- **No-panic / totality.** Stein's algorithm has no documented failure
mode (every `-?` is guarded by a `>`, the final `<<? shift` cannot
overflow because `gcd(a, b) ≤ max(a, b)`).  The function therefore
returns `RustM.ok _` on the entire input domain.  Stated separately
from `gcd_stein_postcondition` because it is the explicit "no failure"
clause of the contract, independent of the returned value. -/
theorem gcd_stein_total (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v :=
  ⟨_, gcd_stein_postcondition a b⟩

/-- **Common-divisor clause (left).** The returned value divides the
first input.  One of the two independent claims certified by the
`result_divides_both_inputs` property test.

Derived from `gcd_stein_postcondition` via `Nat.gcd_dvd_left`; carries
no independent `sorry` (so the only proof obligation remaining is the
closed-form postcondition itself). -/
theorem gcd_stein_divides_a (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧ v.toNat ∣ a.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_left a.toNat b.toNat

/-- **Common-divisor clause (right).** The returned value divides the
second input.  The other independent claim from
`result_divides_both_inputs`.

Derived from `gcd_stein_postcondition` via `Nat.gcd_dvd_right`. -/
theorem gcd_stein_divides_b (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧ v.toNat ∣ b.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_right a.toNat b.toNat

/-- **Greatest-divisor clause.** Every common divisor of `a` and `b`
divides the returned value.  This is the contract certified by the
`result_is_greatest` property test (which checks no integer strictly
greater than the result divides both inputs; equivalently, every
common divisor `d` satisfies `d ∣ gcd`, hence `d ≤ gcd` when both are
nonzero).  Stated in the `d ∣ result` form for parity with
`gcd_while_greatest` and to match `Nat.dvd_gcd`.

Derived from `gcd_stein_postcondition` via `Nat.dvd_gcd`. -/
theorem gcd_stein_greatest (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧
      ∀ d : Nat, d ∣ a.toNat → d ∣ b.toNat → d ∣ v.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  intro d hda hdb
  rw [gcd_toNat_ofNat]
  exact Nat.dvd_gcd hda hdb

end Gcd_stein_u64Obligations
