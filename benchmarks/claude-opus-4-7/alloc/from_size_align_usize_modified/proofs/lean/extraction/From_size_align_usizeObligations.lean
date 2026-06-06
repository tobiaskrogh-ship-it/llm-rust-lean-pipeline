-- Companion obligations file for the `from_size_align_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs are discharged via helper lemmas transferred from the
-- `align_to_usize` / `array_u64` reference patterns (same `Layout` crate family).

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import from_size_align_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace From_size_align_usizeObligations

open from_size_align_usize

/-! ### Helper lemmas (internal scaffolding)

These `private theorem`s reduce the monadic `RustM` plumbing of the
extracted `from_size_align` / `is_size_align_valid` /
`max_size_for_align` / `is_power_of_two_usize`.  They are transferred
almost verbatim from the `align_to_usize` reference (identical
`is_power_of_two_usize`, `Layout`, `LayoutError`) and the `array_u64`
reference (identical add-then-sub `max_size_for_align`). -/

/-- `RustM.ok` is `pure`, so binding it just applies the continuation. -/
private theorem ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    (RustM.ok a) >>= f = f a := rfl

/-- `pure` in `RustM` is `RustM.ok`. -/
private theorem pure_eq_ok {α : Type} (a : α) :
    (pure a : RustM α) = RustM.ok a := rfl

/-- Binding a failed computation propagates the failure. -/
private theorem fail_bind {α β : Type} (e : Error) (f : α → RustM β) :
    (RustM.fail e) >>= f = RustM.fail e := rfl

/-- The Rust `>` extracts to `pure (decide (a > b))`. -/
private theorem hgt (a b : usize) :
    (a >? b) = RustM.ok (decide (a > b)) := rfl

/-! Constant `toNat` reductions (the inlined `isize::MAX (+1)` literal,
the static `1`, and the folded `2^63`). -/

private theorem c63m1_toNat :
    (9223372036854775807 : usize).toNat = 9223372036854775807 := by simp

private theorem c1_toNat : (1 : usize).toNat = 1 := by simp

private theorem c63_toNat :
    (9223372036854775808 : usize).toNat = 9223372036854775808 := by simp

/-- `2^63 - 1 + 1 = 2^63` at `usize` (no overflow).  Proved through
    `toNat` rather than `decide`: a `decide` here makes the kernel
    evaluate a `2^63`-sized `BitVec`/`USize` decision procedure when the
    using theorem (`isav_pow2_core`) is checked, triggering a kernel
    "deep recursion detected" failure.  The `toNat` route folds the
    literal first, keeping the proof kernel-light (same shape as the
    `extend_packed_usize` / `align_to_usize` reference family). -/
private theorem csum_eq :
    (9223372036854775807 : usize) + (1 : usize) = (9223372036854775808 : usize) := by
  apply USize64.toNat_inj.mp
  rw [USize64.toNat_add_of_lt (by rw [c63m1_toNat, c1_toNat]; decide),
      c63m1_toNat, c1_toNat, c63_toNat]

/-- Rust addition does not panic when there is no overflow. -/
private theorem hadd_ok (a b : usize) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a +? b) = RustM.ok (a + b) := by
  have hno : ¬ BitVec.uaddOverflow a.toBitVec b.toBitVec := by
    rw [USize64.uaddOverflow_iff]; omega
  show (if BitVec.uaddOverflow a.toBitVec b.toBitVec
        then (RustM.fail Error.integerOverflow : RustM usize)
        else pure (a + b)) = RustM.ok (a + b)
  rw [if_neg hno]
  rfl

/-- Rust subtraction does not panic when there is no underflow. -/
private theorem hsub_ok (a b : usize) (hba : b.toNat ≤ a.toNat) :
    (a -? b) = RustM.ok (a - b) := by
  have hno : ¬ BitVec.usubOverflow a.toBitVec b.toBitVec := by
    intro hov
    have hso : USize64.subOverflow a b := hov
    rw [USize64.subOverflow_iff] at hso
    omega
  show (if BitVec.usubOverflow a.toBitVec b.toBitVec
        then (RustM.fail Error.integerOverflow : RustM usize)
        else pure (a - b)) = RustM.ok (a - b)
  rw [if_neg hno]
  rfl

/-- A non-zero `usize` is at least `1`. -/
private theorem one_le_of_ne_zero (x : usize) (hx : x ≠ 0) :
    (1 : usize).toNat ≤ x.toNat := by
  have h1 : (1 : usize).toNat = 1 := by simp
  have h0 : (0 : usize).toNat = 0 := by simp
  rw [h1]
  rcases Nat.eq_zero_or_pos x.toNat with hz | hp
  · exact absurd (USize64.toNat_inj.mp (by rw [hz, h0])) hx
  · omega

/-- `max_size_for_align` is total whenever `align ≤ 2^63` (no underflow).
    The extracted body is `(2^63 - 1 + 1) - align`: the `+1` cannot
    overflow (`2^63 - 1 + 1 = 2^63 < 2^64`) and, given the bound, the
    subtraction cannot underflow. -/
private theorem msfa_ok (align : usize)
    (hal : align.toNat ≤ 9223372036854775808) :
    max_size_for_align align
      = RustM.ok ((9223372036854775808 : usize) - align) := by
  unfold max_size_for_align
  rw [hadd_ok (9223372036854775807 : usize) (1 : usize)
        (by rw [c63m1_toNat, c1_toNat]; decide),
      ok_bind, csum_eq,
      hsub_ok (9223372036854775808 : usize) align (by rw [c63_toNat]; exact hal)]

/-- Equational form of `is_power_of_two_usize` for non-zero inputs. The
    extracted body evaluates `x - 1` *unconditionally* (the Rust `&&`
    short-circuit is gone), so totality needs `x ≠ 0`. -/
private theorem ipow2_unfold (x : usize) (hx : x ≠ 0) :
    is_power_of_two_usize x
      = RustM.ok ((x != 0) && ((x &&& (x - 1)) == 0)) := by
  unfold is_power_of_two_usize
  simp only [rust_primitives.cmp.ne, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and, pure_bind]
  rw [hsub_ok x (1 : usize) (one_le_of_ne_zero x hx)]
  rfl

/-- `0 -? 1` underflows and panics (no short-circuit in the extraction). -/
private theorem sub_under_fail :
    ((0 : usize) -? (1 : usize)) = RustM.fail Error.integerOverflow := by
  have hov : BitVec.usubOverflow (0 : usize).toBitVec (1 : usize).toBitVec = true := by
    have hso : USize64.subOverflow (0 : usize) (1 : usize) = true := by
      rw [USize64.subOverflow_iff]; simp
    simpa [USize64.subOverflow] using hso
  show (if BitVec.usubOverflow (0 : usize).toBitVec (1 : usize).toBitVec
        then (RustM.fail Error.integerOverflow : RustM usize)
        else pure ((0 : usize) - 1)) = RustM.fail Error.integerOverflow
  rw [hov]
  rfl

/-- `is_power_of_two_usize 0` panics: the unconditional `0 - 1` underflows. -/
private theorem is_pow2_zero :
    is_power_of_two_usize (0 : usize) = RustM.fail Error.integerOverflow := by
  unfold is_power_of_two_usize
  simp only [rust_primitives.cmp.ne, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and, pure_bind]
  rw [sub_under_fail]
  rfl

/-- A power-of-two `align` is non-zero (otherwise the unconditional
    `x - 1` underflows and `is_power_of_two_usize` fails). -/
private theorem pow2_ne_zero (x : usize)
    (h : is_power_of_two_usize x = RustM.ok true) : x ≠ 0 := by
  rintro rfl
  rw [is_pow2_zero] at h
  exact absurd h (by decide)

/-- A power-of-two `usize` is at most `2^63` (its single set bit is at
    position ≤ 63). This is the structural fact that keeps the inlined
    `max_size_for_align` subtraction from underflowing. -/
private theorem pow2_le (x : usize)
    (h : is_power_of_two_usize x = RustM.ok true) :
    x.toNat ≤ 9223372036854775808 := by
  have hx : x ≠ 0 := pow2_ne_zero x h
  rw [ipow2_unfold x hx] at h
  simp only [RustM.ok] at h
  injection h with h1
  injection h1 with h2
  -- h2 : ((x != 0) && ((x &&& (x - 1)) == 0)) = true
  have hb : x &&& (x - 1) = 0 := by
    rcases hb2 : ((x &&& (x - 1)) == 0) with _ | _
    · rw [hb2, Bool.and_false] at h2
      exact absurd h2 (by decide)
    · simpa using hb2
  have hbit' : x.toBitVec &&& (x.toBitVec - 1#64) = 0#64 := by
    have := congrArg USize64.toBitVec hb
    simpa using this
  have hxb : x.toBitVec ≠ 0#64 := by
    simpa [← USize64.toBitVec_inj] using hx
  clear h2 hb hx
  have hble : x.toBitVec ≤ (9223372036854775808#64 : BitVec 64) := by
    bv_decide
  have hle : x.toBitVec.toNat ≤ (9223372036854775808#64 : BitVec 64).toNat :=
    BitVec.le_def.mp hble
  have hc : (9223372036854775808#64 : BitVec 64).toNat = 9223372036854775808 := by
    have hlt : (9223372036854775808 : Nat) < 2 ^ 64 := by decide
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  show x.toBitVec.toNat ≤ 9223372036854775808
  rw [← hc]; exact hle

/-- The bound `(2^63 - align)` as a `Nat`, given no underflow. -/
private theorem msfa_toNat (align : usize)
    (hal : align.toNat ≤ 9223372036854775808) :
    ((9223372036854775808 : usize) - align).toNat
      = 9223372036854775808 - align.toNat := by
  rw [USize64.toNat_sub_of_le' (by rw [c63_toNat]; exact hal), c63_toNat]

/-! `is_size_align_valid` reductions.  Body:
`if !is_power_of_two_usize align then false
 else if size > max_size_for_align align then false else true`. -/

/-- Non-power-of-two `align` (oracle returns `ok false`): the `!` flips
    it to `true`, the first guard fires, and the helper returns
    `false` — `max_size_for_align` is never reached. -/
private theorem isav_non_pow2 (size align : usize)
    (h : is_power_of_two_usize align = RustM.ok false) :
    is_size_align_valid size align = RustM.ok false := by
  unfold is_size_align_valid
  rw [h]
  rfl

/-- `align = 0`: the unconditional `0 - 1` inside `is_power_of_two_usize`
    underflows, so the whole helper propagates the panic. -/
private theorem isav_zero_fail (size : usize) :
    is_size_align_valid size (0 : usize) = RustM.fail Error.integerOverflow := by
  unfold is_size_align_valid
  rw [is_pow2_zero]
  rfl

/-- Power-of-two `align` (oracle returns `ok true`): the `!` flips it to
    `false`, the first guard is skipped, and the result is decided by the
    size guard `size > 2^63 - align`.

    The truth value `b` of that guard is taken as a parameter with a
    hypothesis `hb`, so `rw [hb]` substitutes it *before* anything forces
    the kernel to reduce the `decide` over the `2^63` literal.  Doing
    `cases` directly on `decide (size > 2^63 - align)` instead makes the
    kernel evaluate that 64-bit `Decidable` instance and triggers a
    "deep recursion detected" failure (same kernel-light shape as the
    `extend_packed_usize` reference's `fsa_core`). -/
private theorem isav_pow2_core (size align : usize) (b : Bool)
    (hpa : is_power_of_two_usize align = RustM.ok true)
    (hb : decide (size > ((9223372036854775808 : usize) - align)) = b) :
    is_size_align_valid size align
      = (if b then RustM.ok false else RustM.ok true) := by
  have hle : align.toNat ≤ 9223372036854775808 := pow2_le align hpa
  unfold is_size_align_valid
  rw [hpa]
  show (max_size_for_align align >>= fun m =>
          (size >? m) >>= fun g => if g then pure false else pure true)
       = (if b then RustM.ok false else RustM.ok true)
  -- Reduce the remaining binds with the *propositional* `ok_bind`/`hgt`
  -- lemmas rather than a `show`-defeq.  A `show` here would force the
  -- kernel to `whnf` `RustM.ok (2^63 - align) >>= …`, dragging the 64-bit
  -- literal through reduction and triggering "deep recursion detected".
  -- (Same kernel-light `rw [msfa_ok …, ok_bind]` / `rw [hgt, hb, ok_bind]`
  -- shape as the `extend_packed_usize` reference's `fsa_core`.)
  rw [msfa_ok align hle, ok_bind, hgt, hb, ok_bind]
  cases b <;> rfl

/-! `from_size_align` reductions.  Body:
`if is_size_align_valid size align then Ok (Layout {size, align}) else Err`. -/

private theorem fsa_true (size align : usize)
    (h : is_size_align_valid size align = RustM.ok true) :
    from_size_align size align
      = RustM.ok (core_models.result.Result.Ok
          (Layout.mk (size := size) (align := align))) := by
  unfold from_size_align
  rw [h]
  rfl

private theorem fsa_false (size align : usize)
    (h : is_size_align_valid size align = RustM.ok false) :
    from_size_align size align
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  unfold from_size_align
  rw [h]
  rfl

private theorem fsa_fail (size align : usize) (e : Error)
    (h : is_size_align_valid size align = RustM.fail e) :
    from_size_align size align = RustM.fail e := by
  unfold from_size_align
  rw [h, fail_bind]

/-! ### Public obligations

`from_size_align size align` validates `align` (must be a power of two)
and `size` (rounded up to `align` must not overflow `isize`), returning
`Ok (Layout { size, align })` or `Err LayoutError`.  The inlined
`max_size_for_align align = (2^63 - 1 + 1) - align = 2^63 - align`, so the
size guard rejects exactly `size > 2^63 - align`.  Because the Rust `&&`
short-circuit is erased in the extraction, `is_power_of_two_usize 0`
evaluates `0 - 1`, underflows, and *panics*; hence `align = 0` makes
`from_size_align` fail rather than return `Err`. -/

/-- Failure condition (non-power-of-two `align`): whenever the
    power-of-two check evaluates to `false` (a non-zero, non-power-of-two
    `align`), `from_size_align` returns `Err(LayoutError)` regardless of
    `size`.

    Captures `prop_non_power_of_two_align_always_errs` (its non-zero
    alignments) and the `from_size_align(8, 3)` assertion of
    `rejects_invalid`.  A buggy implementation that fell through to the
    size check on a non-power-of-two `align` would falsify this. -/
theorem from_size_align_non_pow2_err (size align : usize)
    (h : is_power_of_two_usize align = RustM.ok false) :
    from_size_align size align
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  exact fsa_false size align (isav_non_pow2 size align h)

/-- Failure / model partiality (`align = 0`): the erased `&&`
    short-circuit makes `is_power_of_two_usize 0` evaluate `0 - 1`, which
    underflows, so `from_size_align size 0` panics with
    `Error.integerOverflow`.  (The Rust contract would return `Err`; the
    extracted model diverges here, and this theorem records the model's
    actual behaviour for the `align = 0` sub-case of
    `prop_non_power_of_two_align_always_errs` and the
    `from_size_align(0, 0)` assertion of `rejects_invalid`.) -/
theorem from_size_align_zero_align_fails (size : usize) :
    from_size_align size (0 : usize) = RustM.fail Error.integerOverflow := by
  exact fsa_fail size (0 : usize) Error.integerOverflow (isav_zero_fail size)

/-- Postcondition (valid inputs): when `align` is a power of two and
    `size` fits the inlined bound `2^63 - align`, `from_size_align`
    returns `Ok` with the requested size and alignment reported back
    unchanged.

    Captures the success / size-and-align-preserved half of
    `prop_validity_matches_size_bound`, all of
    `layout_accepts_all_valid_alignments` (the `size = 0` instances), and
    the `from_size_align(24576, 8192)` assertion of `rejects_invalid`.  A
    buggy implementation that mutated the size or alignment would falsify
    this. -/
theorem from_size_align_ok_within_bound (size align : usize)
    (hpa : is_power_of_two_usize align = RustM.ok true)
    (hsize : size.toNat ≤ 9223372036854775808 - align.toNat) :
    from_size_align size align
      = RustM.ok (core_models.result.Result.Ok
          (Layout.mk (size := size) (align := align))) := by
  have hle : align.toNat ≤ 9223372036854775808 := pow2_le align hpa
  have hcond : decide (size > ((9223372036854775808 : usize) - align)) = false := by
    rw [decide_eq_false_iff_not, gt_iff_lt, USize64.lt_iff_toNat_lt,
        msfa_toNat align hle]
    omega
  apply fsa_true
  simpa using isav_pow2_core size align false hpa hcond

/-- Failure condition (size overflow): when `align` is a power of two but
    `size` strictly exceeds the inlined bound `2^63 - align`, the rounded
    size would overflow `isize`, so `from_size_align` returns
    `Err(LayoutError)` — and returns it as `RustM.ok (Err …)`, i.e. it
    does NOT panic.

    Captures the failure half of `prop_validity_matches_size_bound` and
    the boundary edge cases of `layout_round_up_to_align_edge_cases`.  A
    buggy implementation that omitted the size guard would falsify
    this. -/
theorem from_size_align_size_overflow_err (size align : usize)
    (hpa : is_power_of_two_usize align = RustM.ok true)
    (hsize : 9223372036854775808 - align.toNat < size.toNat) :
    from_size_align size align
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  have hle : align.toNat ≤ 9223372036854775808 := pow2_le align hpa
  have hcond : decide (size > ((9223372036854775808 : usize) - align)) = true := by
    rw [decide_eq_true_eq, gt_iff_lt, USize64.lt_iff_toNat_lt,
        msfa_toNat align hle]
    omega
  apply fsa_false
  simpa using isav_pow2_core size align true hpa hcond

/-- Totality / no-panic for valid alignment: for every `size` and every
    power-of-two `align`, `from_size_align` returns a value successfully
    (never `RustM.fail`).  The power-of-two hypothesis bounds
    `align ≤ 2^63`, keeping the inlined `max_size_for_align` subtraction
    from underflowing.

    Captures the implicit "never panics for a valid alignment" clause of
    `prop_validity_matches_size_bound` (the test pattern-matches only on
    `Ok`/`Err`, never expecting a panic). -/
theorem from_size_align_total_for_pow2 (size align : usize)
    (hpa : is_power_of_two_usize align = RustM.ok true) :
    ∃ r : core_models.result.Result Layout LayoutError,
      from_size_align size align = RustM.ok r := by
  by_cases hc : size.toNat ≤ 9223372036854775808 - align.toNat
  · exact ⟨_, from_size_align_ok_within_bound size align hpa hc⟩
  · exact ⟨_, from_size_align_size_overflow_err size align hpa (by omega)⟩

/-! ### Concrete unit-test obligations (`rejects_invalid`) -/

/-- `from_size_align(8, 3)` errors: `3` is not a power of two
    (`3 & 2 = 2 ≠ 0`). -/
theorem from_size_align_8_3_err :
    from_size_align (8 : usize) (3 : usize)
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  apply from_size_align_non_pow2_err
  decide

/-- `from_size_align(0, 0)` panics in the extracted model:
    `is_power_of_two_usize 0` underflows on `0 - 1` (the Rust contract
    would return `Err`). -/
theorem from_size_align_0_0_fails :
    from_size_align (0 : usize) (0 : usize)
      = RustM.fail Error.integerOverflow := by
  exact from_size_align_zero_align_fails (0 : usize)

/-- `from_size_align(24576, 8192)` succeeds: `8192 = 2^13` is a power of
    two and `24576 ≤ 2^63 - 8192`, so it reports the requested size and
    alignment. -/
theorem from_size_align_24576_8192_ok :
    from_size_align (24576 : usize) (8192 : usize)
      = RustM.ok (core_models.result.Result.Ok
          (Layout.mk (size := (24576 : usize)) (align := (8192 : usize)))) := by
  apply from_size_align_ok_within_bound
  · decide
  · simp

end From_size_align_usizeObligations
