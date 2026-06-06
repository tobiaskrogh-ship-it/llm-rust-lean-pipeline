-- Companion obligations file for the `is_size_align_valid_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import is_size_align_valid_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Is_size_align_valid_usizeObligations

open is_size_align_valid_usize

/-! ## Numeric / bit-trick helper lemmas (pure, no monad) -/

/-- `(1 : usize)` has `toNat = 1`. -/
private theorem one_toNat : (1 : usize).toNat = 1 :=
  USize64.toNat_ofNat_of_lt (by decide)

/-- The `2^63` constant as a `usize` has `toNat = 9223372036854775808`. -/
private theorem big_toNat :
    ((9223372036854775808 : usize)).toNat = 9223372036854775808 :=
  USize64.toNat_ofNat_of_lt (by decide)

/-- `pure` and `RustM.ok` coincide on `RustM` (definitional). -/
private theorem pure_eq_ok {α : Type} (v : α) :
    (pure v : RustM α) = RustM.ok v := rfl

/-- Binding after a failure short-circuits: `RustM = ExceptT Error Option`,
    so a `.fail` is propagated unchanged by `>>=` (definitional). -/
private theorem fail_bind {α β : Type} (e : Error) (f : α → RustM β) :
    (RustM.fail e >>= f) = RustM.fail e := rfl

/-- Mapping over a failure is a no-op: `Functor.map` propagates a `.fail`
    unchanged on `RustM` (definitional). The bind-chain of a `do`-block
    whose only effectful action is a `.fail` collapses (via `bind_pure_comp`)
    to `g <$> RustM.fail e`, so this is the lemma that closes it. -/
private theorem fail_map {α β : Type} (e : Error) (g : α → β) :
    (g <$> (RustM.fail e : RustM α)) = RustM.fail e := rfl

/-- `RustM.fail e` and `RustM.ok v` are distinct: `RustM = ExceptT Error
    Option`, so these are `some (Except.error e)` vs `some (Except.ok v)`,
    two different `Except` constructors. This makes the residual goals of
    the `align = 0` instances below (`RustM.fail .. = RustM.ok ..` and
    `∃ v, RustM.fail .. = RustM.ok v`) genuinely **False**, not merely
    unproven — the surviving `sorry`s sit on a provably unsatisfiable goal,
    so no Lean-side tactic can close them. -/
private theorem fail_ne_ok {α : Type} (e : Error) (v : α) :
    (RustM.fail e : RustM α) ≠ RustM.ok v := by
  simp [RustM.fail, RustM.ok]

/-- An unsigned subtraction does not underflow whenever the subtrahend is
    `≤` the minuend (at the `Nat` level). -/
private theorem usub_false {x y : usize} (h : y.toNat ≤ x.toNat) :
    BitVec.usubOverflow x.toBitVec y.toBitVec = false := by
  have hnlt : ¬ (x.toBitVec.toNat < y.toBitVec.toNat) := by
    simp only [USize64.toNat_toBitVec]; omega
  simpa [BitVec.usubOverflow] using hnlt

/-- A `usize` that is not `0` has `toNat ≠ 0`. -/
private theorem toNat_ne_zero {n : usize} (h : n ≠ (0 : usize)) : n.toNat ≠ 0 := by
  intro hc
  apply h
  apply USize64.toNat_inj.mp
  rw [hc, USize64.toNat_zero]

/-- `toNat` distributes over the `usize` bitwise AND. -/
private theorem usize_toNat_and (a b : usize) :
    (a &&& b).toNat = a.toNat &&& b.toNat := by
  exact BitVec.toNat_and a.toBitVec b.toBitVec

/-- Bridge: the `usize` bitwise expression `align &&& (align - 1)` has the
    `Nat` value `align.toNat &&& (align.toNat - 1)` when `align ≠ 0`. -/
private theorem and_pred_toNat {align : usize} (h : align ≠ (0 : usize)) :
    (align &&& (align - 1)).toNat = align.toNat &&& (align.toNat - 1) := by
  have hne' : align.toNat ≠ 0 := toNat_ne_zero h
  have h1le : (1 : usize) ≤ align := by
    rw [USize64.le_iff_toNat_le, one_toNat]; omega
  have hsub : (align - 1).toNat = align.toNat - 1 := by
    rw [USize64.toNat_sub_of_le align 1 h1le, one_toNat]
  rw [usize_toNat_and, hsub]

/-- Core power-of-two characterisation, transported from
    `Nat.and_sub_one_eq_zero_iff_isPowerOfTwo`: for `align ≠ 0`,
    `align & (align - 1) = 0` exactly when `align.toNat` is a power of two. -/
private theorem pow2_iff (align : usize) (hne : align ≠ (0 : usize)) :
    (align &&& (align - 1)) = (0 : usize) ↔ ∃ k : Nat, align.toNat = 2 ^ k := by
  have hne' : align.toNat ≠ 0 := toNat_ne_zero hne
  have hand : (align &&& (align - 1)).toNat = align.toNat &&& (align.toNat - 1) :=
    and_pred_toNat hne
  constructor
  · intro hcc
    have hN : align.toNat &&& (align.toNat - 1) = 0 := by
      have hh := congrArg USize64.toNat hcc
      rw [hand, USize64.toNat_zero] at hh
      exact hh
    exact (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hne').mp hN
  · intro hpow
    have hN : align.toNat &&& (align.toNat - 1) = 0 :=
      (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hne').mpr hpow
    apply USize64.toNat_inj.mp
    rw [hand, USize64.toNat_zero]
    exact hN

/-- If `align.toNat = 2 ^ k` then `align.toNat ≤ 2 ^ 63`
    (since `align.toNat < 2^64`). -/
private theorem pow2_le {align : usize} {k : Nat} (h : align.toNat = 2 ^ k) :
    align.toNat ≤ 2 ^ 63 := by
  have hlt : align.toNat < 2 ^ 64 := USize64.toNat_lt align
  have hk63 : k ≤ 63 := by
    rcases Nat.lt_or_ge k 64 with hk | hk
    · omega
    · exfalso
      have hge : (2:Nat) ^ 64 ≤ 2 ^ k :=
        Nat.pow_le_pow_right (n := 2) (by decide) hk
      rw [h] at hlt
      omega
  rw [h]
  exact Nat.pow_le_pow_right (n := 2) (by decide) hk63

/-- The round-up arithmetic equivalence: for a power-of-two divisor
    `A = 2 ^ k` (`k ≤ 63`, so `A ∣ 2^63`),
    `⌈s / A⌉ * A ≤ 2^63 - 1` exactly when `s ≤ 2^63 - A`.

    This is the bridge between the implementation's subtraction-based
    comparison `size ≤ (2^63 - align)` and the documented round-up
    postcondition `next_multiple_of(size, align) ≤ isize::MAX`. -/
private theorem round_up_le_iff {s A q : Nat} (hA : 0 < A)
    (hq : 2 ^ 63 = A * q) :
    ((s + (A - 1)) / A * A ≤ 2 ^ 63 - 1) ↔ s ≤ 2 ^ 63 - A := by
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hz0 | hz0
    · exfalso; rw [hz0, Nat.mul_zero] at hq; omega
    · exact hz0
  have hAq : 0 < A * q := Nat.mul_pos hA hqpos
  have hAle : A ≤ 2 ^ 63 := by
    rw [hq]; exact Nat.le_mul_of_pos_right A hqpos
  have h1 : ((s + (A - 1)) / A * A ≤ 2 ^ 63 - 1)
              ↔ (s + (A - 1)) / A < q := by
    rw [hq]
    constructor
    · intro hh
      have hlt : (s + (A - 1)) / A * A < A * q := by omega
      have hlt' : (s + (A - 1)) / A * A < q * A := by
        rw [Nat.mul_comm q A]; exact hlt
      exact (Nat.mul_lt_mul_right hA).mp hlt'
    · intro hh
      have hlt' : (s + (A - 1)) / A * A < q * A :=
        (Nat.mul_lt_mul_right hA).mpr hh
      have hlt : (s + (A - 1)) / A * A < A * q := by
        rw [Nat.mul_comm A q]; exact hlt'
      omega
  have h2 : ((s + (A - 1)) / A < q) ↔ s ≤ 2 ^ 63 - A := by
    rw [Nat.lt_iff_le_pred hqpos, Nat.div_le_iff_le_mul_add_pred hA]
    have hmul : A * (q - 1) = 2 ^ 63 - A := by
      rw [Nat.mul_sub_one, ← hq]
    omega
  rw [h1, h2]

/-! ## Evaluation of the extracted `RustM` program -/

/-- `is_power_of_two_usize n` for `n ≠ 0`: the short-circuit guard `n != 0`
    is `true`, the subtraction `n - 1` does not underflow, and the result
    is the bit-trick boolean. -/
private theorem ipot_eval (n : usize) (hn : n ≠ (0 : usize)) :
    is_power_of_two_usize n
      = pure ((n != (0 : usize)) && ((n &&& (n - 1)) == (0 : usize))) := by
  have hn' : n.toNat ≠ 0 := toNat_ne_zero hn
  have h_no : BitVec.usubOverflow n.toBitVec (1 : usize).toBitVec = false := by
    apply usub_false
    rw [one_toNat]; omega
  have h_eq : (n -? (1 : usize) : RustM usize) = pure (n - 1) := by
    show (rust_primitives.ops.arith.Sub.sub n (1 : usize) : RustM usize)
          = pure (n - 1)
    show (if BitVec.usubOverflow n.toBitVec (1 : usize).toBitVec then
            (.fail .integerOverflow : RustM usize) else pure (n - 1))
          = pure (n - 1)
    rw [show BitVec.usubOverflow n.toBitVec (1 : usize).toBitVec = false from h_no]
    rfl
  unfold is_power_of_two_usize
  simp only [rust_primitives.cmp.ne, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and]
  rw [h_eq]
  simp

/-- `max_size_for_align align` when `align.toNat ≤ 2^63`: the subtraction
    `2^63 - align` does not underflow. -/
private theorem msfa_eval (align : usize) (hle : align.toNat ≤ 2 ^ 63) :
    max_size_for_align align = pure ((9223372036854775808 : usize) - align) := by
  have h_no : BitVec.usubOverflow ((9223372036854775808 : usize)).toBitVec
                align.toBitVec = false := by
    apply usub_false
    rw [big_toNat]; omega
  have h_eq : ((9223372036854775808 : usize) -? align : RustM usize)
              = pure ((9223372036854775808 : usize) - align) := by
    show (rust_primitives.ops.arith.Sub.sub (9223372036854775808 : usize) align
            : RustM usize)
          = pure ((9223372036854775808 : usize) - align)
    show (if BitVec.usubOverflow ((9223372036854775808 : usize)).toBitVec
              align.toBitVec then
            (.fail .integerOverflow : RustM usize)
          else pure ((9223372036854775808 : usize) - align))
          = pure ((9223372036854775808 : usize) - align)
    rw [show BitVec.usubOverflow ((9223372036854775808 : usize)).toBitVec
              align.toBitVec = false from h_no]
    rfl
  unfold max_size_for_align
  rw [h_eq]

/-- Evaluation of `is_size_align_valid` on a non-power-of-two, non-zero
    alignment: the bit-trick test fails, so the function rejects with
    `false` without ever evaluating `max_size_for_align`. -/
private theorem isav_eval_notpow2 (size align : usize) (hz : align ≠ (0 : usize))
    (hnp : (align &&& (align - 1)) ≠ (0 : usize)) :
    is_size_align_valid size align = pure false := by
  have hb1 : (align != (0 : usize)) = true := by simp [hz]
  have hb2 : ((align &&& (align - 1)) == (0 : usize)) = false := by simp [hnp]
  unfold is_size_align_valid
  rw [ipot_eval align hz]
  simp [hb1, hb2]

/-- Evaluation of `is_size_align_valid` on a power-of-two alignment
    (`align ≠ 0`, `align & (align-1) = 0`, `align.toNat ≤ 2^63`): the
    bit-trick test passes, so the result is the size/round-up comparison. -/
private theorem isav_eval_pow2 (size align : usize) (hz : align ≠ (0 : usize))
    (hp : (align &&& (align - 1)) = (0 : usize)) (hle : align.toNat ≤ 2 ^ 63) :
    is_size_align_valid size align
      = (if ((9223372036854775808 : usize) - align) < size
         then pure false else pure true) := by
  have hb1 : (align != (0 : usize)) = true := by simp [hz]
  have hb2 : ((align &&& (align - 1)) == (0 : usize)) = true := by simp [hp]
  unfold is_size_align_valid
  rw [ipot_eval align hz, msfa_eval align hle]
  simp [hb1, hb2, rust_primitives.cmp.gt]

/-! ## Zero alignment: the extracted model fails (lost short-circuit `&&`) -/

/-- The 64-bit unsigned subtraction `0 - 1` overflows. -/
private theorem usub_zero_one_overflow :
    BitVec.usubOverflow (0 : usize).toBitVec (1 : usize).toBitVec = true := by
  simp [BitVec.usubOverflow]

/-- Machine-checked extraction artifact. Hax lowers Rust's short-circuit
    `n != 0 && (n & (n-1)) == 0` to the **strict** `RustM` conjunction
    `rust_primitives.hax.logical_op.and` (`fun a b => pure (a && b)`), and
    the surrounding `do`-block hoists `(← (n -? 1))` unconditionally. Hence
    for `n = 0` the subtraction `0 -? 1` underflows, and
    `is_power_of_two_usize 0` evaluates to `RustM.fail .integerOverflow` —
    **not** `RustM.ok false`, which the intended Rust contract (whose `&&`
    short-circuits, never reaching `0 - 1`) would give. -/
private theorem ipot_zero :
    is_power_of_two_usize (0 : usize) = RustM.fail Error.integerOverflow := by
  have h_eq : ((0 : usize) -? (1 : usize) : RustM usize)
                = RustM.fail Error.integerOverflow := by
    show (rust_primitives.ops.arith.Sub.sub (0 : usize) (1 : usize) : RustM usize)
          = RustM.fail Error.integerOverflow
    show (if BitVec.usubOverflow (0 : usize).toBitVec (1 : usize).toBitVec then
            (.fail .integerOverflow : RustM usize) else pure ((0 : usize) - 1))
          = RustM.fail Error.integerOverflow
    rw [show BitVec.usubOverflow (0 : usize).toBitVec (1 : usize).toBitVec = true
          from usub_zero_one_overflow]
    simp
  unfold is_power_of_two_usize
  simp only [rust_primitives.cmp.ne, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and]
  rw [h_eq]
  simp [fail_map]

/-- Machine-checked extraction artifact at the top level: because
    `is_power_of_two_usize 0` fails (`ipot_zero`) and `RustM` bind
    propagates failure (`fail_bind`), the whole checker fails for
    `align = 0`, irrespective of `size`. The intended Rust contract
    returns `false` here (Rust's short-circuit `&&` makes `0 - 1`
    unreachable), so this equation pins the precise discrepancy between
    the extracted model and the source contract. -/
private theorem isav_zero_fails (size : usize) :
    is_size_align_valid size (0 : usize) = RustM.fail Error.integerOverflow := by
  unfold is_size_align_valid
  rw [ipot_zero]
  simp [fail_bind]

/-! ## Obligations -/

/-- Contract clause 1 (failure / precondition: invalid alignment is rejected).

    `Layout::from_size_align` requires `align` to be a power of two
    (`Alignment::new(align)` is `None` otherwise — including `align = 0`).
    Whenever `align` is **not** a power of two, `is_size_align_valid` must
    reject the input by returning `false`, *independently of* `size`.

    Captures the property test `non_power_of_two_align_always_rejected`
    and the unit test `rejects_non_power_of_two`. A "power of two" is the
    mathematical predicate `∃ k, align = 2^k`; `0` satisfies its negation.

    STUCK SUB-GOAL (only the `align = 0` instance): after the substantive
    attempt `rw [isav_zero_fails size]` the goal is the constructor clash

        `RustM.fail Error.integerOverflow = RustM.ok false`

    i.e. `some (Except.error .integerOverflow) = some (Except.ok false)` —
    two distinct `Except` constructors — which is genuinely **False**
    (machine-certified by `fail_ne_ok`), not merely unproven. The reduction
    is *also* machine-checked: `isav_zero_fails : is_size_align_valid size 0
    = RustM.fail Error.integerOverflow`, proved from `ipot_zero`, which
    shows Hax lowers Rust's short-circuit `&&` to the strict
    `rust_primitives.hax.logical_op.and` while the `do`-block hoists
    `(← (0 -? 1))` unconditionally, so `0 -? 1` underflows
    (`usub_zero_one_overflow`). The clause is true of the *intended* Rust
    contract (whose `&&` short-circuits and never reaches `0 - 1`) but
    false of the mechanically-extracted function at `align = 0`. The
    `align ≠ 0` case (the substantive content of the clause) is fully
    proved below.

    STRUCTURAL UNBLOCK: a Hax extraction fix that preserves Rust's
    short-circuit `&&` (lowering `a && b` to a guarded `if a then b else
    false` in `RustM` rather than `logical_op.and (← a) (← b)` with both
    operands force-sequenced) would make `is_power_of_two_usize 0 =
    RustM.ok false` and close this instance in one line. Not fixable
    Lean-side: editing the extracted module is out of scope (harness-
    rejected), and `isav_zero_fails`/`fail_ne_ok` prove no Lean tactic can
    reconcile `RustM.fail` with `RustM.ok`. -/
theorem is_size_align_valid_non_power_of_two_rejected
    (size align : usize) (h : ¬ ∃ k : Nat, align.toNat = 2 ^ k) :
    is_size_align_valid size align = RustM.ok false := by
  by_cases hz : align = (0 : usize)
  · -- align = 0: the extracted checker provably fails with
    -- `.integerOverflow` (machine-checked by `isav_zero_fails`), because
    -- Hax lost Rust's short-circuit `&&`. After this rewrite the goal is
    -- the constructor clash `RustM.fail Error.integerOverflow =
    -- RustM.ok false`, which `fail_ne_ok` shows is genuinely False, so it
    -- is unclosable Lean-side. Documented intractable sorry (see docstring).
    subst hz
    rw [isav_zero_fails size]
    sorry
  · -- align ≠ 0 and not a power of two ⟹ bit-trick test ≠ 0 ⟹ ok false.
    have hnp : (align &&& (align - 1)) ≠ (0 : usize) := by
      intro hcc
      exact h ((pow2_iff align hz).mp hcc)
    exact (isav_eval_notpow2 size align hz hnp).trans (pure_eq_ok false)

/-- Contract clause 2 (postcondition for valid alignment).

    For every power-of-two `align`, the result is exactly the documented
    property: `size` rounded up to the next multiple of `align` must not
    exceed `isize::MAX` (`= 2^63 - 1` on a 64-bit target). The round-up is
    expressed at the `Nat` level as `((size + (align - 1)) / align) * align`
    — exactly the overflow-safe `u128` oracle `fits_when_rounded_up` used
    by the Rust tests.

    Captures the property test `power_of_two_align_matches_round_up_contract`
    and the unit test `layout_round_up_to_align_edge_cases`. -/
theorem is_size_align_valid_power_of_two_round_up
    (size align : usize) (k : Nat) (h : align.toNat = 2 ^ k) :
    is_size_align_valid size align
      = RustM.ok (decide
          (((size.toNat + (align.toNat - 1)) / align.toNat) * align.toNat
            ≤ 2 ^ 63 - 1)) := by
  -- A power of two is non-zero.
  have hApos : 0 < align.toNat := by rw [h]; exact Nat.two_pow_pos k
  have hz : align ≠ (0 : usize) := by
    intro hc; subst hc; simp [USize64.toNat_zero] at hApos
  -- bit-trick test passes, bound for the second subtraction holds.
  have hp : (align &&& (align - 1)) = (0 : usize) :=
    (pow2_iff align hz).mpr ⟨k, h⟩
  have hle : align.toNat ≤ 2 ^ 63 := pow2_le h
  -- k ≤ 63 and the divisibility witness `2^63 = align.toNat * 2^(63-k)`.
  have hk63 : k ≤ 63 := by
    rcases Nat.lt_or_ge k 64 with hk | hk
    · omega
    · exfalso
      have hge : (2:Nat) ^ 64 ≤ 2 ^ k :=
        Nat.pow_le_pow_right (n := 2) (by decide) hk
      have hlt : align.toNat < 2 ^ 64 := USize64.toNat_lt align
      rw [h] at hlt; omega
  have hq : 2 ^ 63 = align.toNat * 2 ^ (63 - k) := by
    rw [h, ← Nat.pow_add]
    congr 1
    omega
  -- evaluate the program to the size comparison
  rw [isav_eval_pow2 size align hz hp hle]
  -- bridge `(2^63 - align) : usize` to its `Nat` value
  have hmle : align ≤ (9223372036854775808 : usize) := by
    rw [USize64.le_iff_toNat_le, big_toNat]; omega
  have hm : ((9223372036854775808 : usize) - align).toNat
              = 2 ^ 63 - align.toNat := by
    rw [USize64.toNat_sub_of_le _ _ hmle, big_toNat]
  -- relate the `usize` comparison to the round-up bound
  have hround : (((size.toNat + (align.toNat - 1)) / align.toNat) * align.toNat
                  ≤ 2 ^ 63 - 1)
                ↔ size.toNat ≤ 2 ^ 63 - align.toNat :=
    round_up_le_iff hApos hq
  by_cases hcmp : ((9223372036854775808 : usize) - align) < size
  · rw [if_pos hcmp]
    have hgt : 2 ^ 63 - align.toNat < size.toNat := by
      have hh := hcmp
      rw [USize64.lt_iff_toNat_lt, hm] at hh
      exact hh
    have hnotP : ¬ (((size.toNat + (align.toNat - 1)) / align.toNat)
                      * align.toNat ≤ 2 ^ 63 - 1) := by
      rw [hround]; omega
    rw [decide_eq_false hnotP, pure_eq_ok]
  · rw [if_neg hcmp]
    have hle2 : size.toNat ≤ 2 ^ 63 - align.toNat := by
      have hh : ¬ (((9223372036854775808 : usize) - align) < size) := hcmp
      rw [USize64.lt_iff_toNat_lt, hm] at hh
      omega
    have hyesP : ((size.toNat + (align.toNat - 1)) / align.toNat)
                    * align.toNat ≤ 2 ^ 63 - 1 := by
      rw [hround]; exact hle2
    rw [decide_eq_true hyesP, pure_eq_ok]

/-- Documented no-panic / totality clause.

    The Rust source explicitly relies on the short-circuit `&&` so that
    `n - 1` "never underflows when `n == 0`", and `max_size_for_align`'s
    subtraction `2^63 - align` never underflows for a power-of-two `align`.
    Hence `is_size_align_valid` is a total `bool`-valued checker.

    STUCK SUB-GOAL (only the `align = 0` instance): after the substantive
    attempt `rw [isav_zero_fails size]` the goal is

        `∃ v : Bool, RustM.fail Error.integerOverflow = RustM.ok v`

    which is genuinely **False**: by `fail_ne_ok` no `v` reconciles a
    `RustM.fail` (`some (Except.error ..)`) with a `RustM.ok`
    (`some (Except.ok ..)`). The reduction `isav_zero_fails :
    is_size_align_valid size 0 = RustM.fail Error.integerOverflow` is
    machine-checked (from `ipot_zero`): Hax lost Rust's short-circuit `&&`,
    so the unconditional `(← (0 -? 1))` underflows. The totality clause is
    true of the intended Rust function (short-circuit `&&` makes `0 - 1`
    unreachable) but false of the extracted model at `align = 0`. The
    `align ≠ 0` case is fully proved below.

    STRUCTURAL UNBLOCK: the same Hax extraction fix described on
    `is_size_align_valid_non_power_of_two_rejected` (preserve short-circuit
    `&&` as a guarded `if`) makes `is_size_align_valid size 0 = RustM.ok
    false`, discharging this instance. Not fixable Lean-side:
    `isav_zero_fails`/`fail_ne_ok` machine-prove the residual is
    unsatisfiable, and the extracted module is harness-rejected for edits. -/
theorem is_size_align_valid_no_panic (size align : usize) :
    ∃ v : Bool, is_size_align_valid size align = RustM.ok v := by
  by_cases hz : align = (0 : usize)
  · -- align = 0: extraction artifact (lost short-circuit `&&`). Documented
    -- intractable sorry (see docstring).
    subst hz
    sorry
  · -- align ≠ 0: split on the bit-trick test.
    by_cases hp : (align &&& (align - 1)) = (0 : usize)
    · -- power of two ⟹ obligation 2 gives an explicit `RustM.ok` value.
      obtain ⟨k, hk⟩ := (pow2_iff align hz).mp hp
      exact ⟨_, is_size_align_valid_power_of_two_round_up size align k hk⟩
    · -- not a power of two ⟹ rejects with `false`.
      exact ⟨false, (isav_eval_notpow2 size align hz hp).trans (pure_eq_ok false)⟩

end Is_size_align_valid_usizeObligations
