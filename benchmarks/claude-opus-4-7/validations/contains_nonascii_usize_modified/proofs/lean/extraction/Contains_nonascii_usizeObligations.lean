-- Companion obligations file for the `contains_nonascii_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import contains_nonascii_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Contains_nonascii_usizeObligations

/-- Specification oracle, deliberately independent of the implementation's
    bit-mask trick. A 64-bit word "contains nonascii" iff at least one of
    its eight bytes has value `≥ 0x80` (i.e. its high bit is set). Byte `i`
    is extracted at the `Nat` level as `(x.toNat / 2 ^ (8 * i)) % 256`. The
    disjunction ranges over all eight byte positions, so it is independent
    of host byte order and faithfully models the Rust oracle
    `x.to_ne_bytes().iter().any(|&b| b >= 0x80)` (native-endian on the
    64-bit test host = little-endian byte extraction). -/
private def hasNonasciiByte (x : usize) : Bool :=
  (List.range 8).any (fun i => decide ((x.toNat / 2 ^ (8 * i)) % 256 ≥ 128))

/-! ## Scaffolding.

`contains_nonascii` is a straight-line, total word function: one bitwise
AND (`&&&?`, which is `pure (· &&& ·)`) bound into one `!=? 0` comparison
(`rust_primitives.cmp.ne`, which is `pure (· != ·)`). Both legs are pure,
so the whole computation reduces definitionally to a single `RustM.ok` of
a `Bool`. -/

/-- The `RustM` computation collapses to `RustM.ok ((x &&& MASK) != 0)`.
    Mirrors the `is_zero` reference pattern (`do (x ==? 0)` reduces by
    `rfl`); here the extra `←` bind on the pure `&&&?` collapses by the
    `Option`/`ExceptT` monad laws, which hold definitionally. -/
private theorem contains_nonascii_unfold (x : usize) :
    contains_nonascii_usize.contains_nonascii x =
      RustM.ok ((x &&& contains_nonascii_usize.NONASCII_MASK) != (0 : usize)) := by
  rfl

/-- Pure-`Nat` characterisation of "byte `≥ 128`": the high bit of the
    `E`-th byte of `n` is set iff bit `E + 7` of `n` is set. `omega`
    discharges the residual constant-modulus identity. -/
private theorem byte_high_iff (n E : Nat) :
    decide ((n / 2 ^ E) % 256 ≥ 128) = decide (n / 2 ^ (E + 7) % 2 = 1) := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize n / 2 ^ E = m
  simp only [Nat.reducePow, decide_eq_decide]
  omega

/-- Per-byte high-bit test as a single `BitVec` bit of `x`. Bridges the
    `Nat`-level oracle to `getLsbD`, which `bv_decide` reflects natively
    (unlike `BitVec.toNat`, which it abstracts as opaque). -/
private theorem byte_bit (x : usize) (E : Nat) :
    decide ((x.toNat / 2 ^ E) % 256 ≥ 128) = x.toBitVec.getLsbD (E + 7) := by
  rw [byte_high_iff, ← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
      USize64.toNat_toBitVec]

/-- `hasNonasciiByte` unfolded to the explicit eight-way disjunction. The
    `List.range 8 |>.any` recursion reduces by `rfl` (kernel computation of
    `List.range` and `List.any`); the right-associated shape with the
    trailing `|| false` matches `List.any`'s definitional unfolding. -/
private theorem hasNonasciiByte_expand (x : usize) :
    hasNonasciiByte x =
      (decide ((x.toNat / 2 ^ (8 * 0)) % 256 ≥ 128) ||
      (decide ((x.toNat / 2 ^ (8 * 1)) % 256 ≥ 128) ||
      (decide ((x.toNat / 2 ^ (8 * 2)) % 256 ≥ 128) ||
      (decide ((x.toNat / 2 ^ (8 * 3)) % 256 ≥ 128) ||
      (decide ((x.toNat / 2 ^ (8 * 4)) % 256 ≥ 128) ||
      (decide ((x.toNat / 2 ^ (8 * 5)) % 256 ≥ 128) ||
      (decide ((x.toNat / 2 ^ (8 * 6)) % 256 ≥ 128) ||
      (decide ((x.toNat / 2 ^ (8 * 7)) % 256 ≥ 128) || false)))))))) := by
  unfold hasNonasciiByte
  rfl

/-- The `usize`-level mask test reduced to the underlying `BitVec 64`.
    `usize` (`= USize64`) is a custom struct that `bv_decide` does not
    reflect, so this lemma peels the wrapper. `usize` derives `BEq` from
    its `DecidableEq` (hence `LawfulBEq`), and `(a &&& b).toBitVec`,
    `(0 : usize).toBitVec`, `(c : usize).toBitVec` are all definitional, so
    the case split on the `BitVec` equality discharges both Bools. -/
private theorem mask_test_bv (x : usize) :
    ((x &&& contains_nonascii_usize.NONASCII_MASK) != (0 : usize))
      = decide (x.toBitVec &&& (9259542123273814144 : BitVec 64) ≠ (0 : BitVec 64)) := by
  unfold contains_nonascii_usize.NONASCII_MASK
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, decide_eq_true_eq, ne_eq]
  constructor
  · intro hne hbv
    exact hne (USize64.eq_of_toBitVec_eq (by exact hbv))
  · intro hbv hne
    exact hbv (USize64.toBitVec_eq_of_eq hne)

/-- Failure condition: `contains_nonascii` is total. It has no precondition,
    performs only a bitwise-AND followed by a `!= 0` comparison (neither can
    panic, error, or overflow), and returns a plain `bool`, so the call
    succeeds on every `usize` input. (Rust source: "total — no precondition,
    never panics, returns a plain bool"; the absence of any `#[should_panic]`
    / failure-mode test confirms there is no failure clause to violate.) -/
theorem contains_nonascii_no_failure (x : usize) :
    ∃ v : Bool, contains_nonascii_usize.contains_nonascii x = RustM.ok v :=
  ⟨(x &&& contains_nonascii_usize.NONASCII_MASK) != (0 : usize),
   contains_nonascii_unfold x⟩

/-- Postcondition (functional correctness): the returned bool equals the
    per-byte high-bit disjunction — `true` exactly when some native-endian
    byte of `x` is `≥ 0x80`, `false` otherwise. This is the single semantic
    claim certified by the Rust property test
    `result_equals_per_byte_high_bit_oracle`, whose oracle
    `spec_contains_nonascii` is `x.to_ne_bytes().iter().any(|&b| b >= 0x80)`,
    deliberately independent of the masking implementation. -/
theorem contains_nonascii_postcondition (x : usize) :
    contains_nonascii_usize.contains_nonascii x = RustM.ok (hasNonasciiByte x) := by
  rw [contains_nonascii_unfold]
  congr 1
  rw [hasNonasciiByte_expand x]
  rw [byte_bit x (8 * 0), byte_bit x (8 * 1), byte_bit x (8 * 2),
      byte_bit x (8 * 3), byte_bit x (8 * 4), byte_bit x (8 * 5),
      byte_bit x (8 * 6), byte_bit x (8 * 7)]
  rw [mask_test_bv x]
  simp only [Nat.reduceMul, Nat.reduceAdd]
  bv_decide

end Contains_nonascii_usizeObligations
