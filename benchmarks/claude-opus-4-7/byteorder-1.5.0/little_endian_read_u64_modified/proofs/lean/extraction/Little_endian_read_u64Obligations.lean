-- Companion obligations file for the `little_endian_read_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import little_endian_read_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

namespace Little_endian_read_u64Obligations

/-! ## Specification oracle: little-endian decode of the first 8 bytes.

`leDecode buf` is the `Nat` value of the 8 bytes `buf[0], buf[1], …,
buf[7]` read **little-endian**: the byte at the *lowest* index (`buf[0]`)
is the *least* significant (weight `2^0`) and `buf[7]` is the most
significant (weight `2^56`). It is expressed at the `Nat` level,
independent of the implementation's cast/shift/OR form, so the
postcondition is a genuine semantic specification rather than a
restatement of the code. It mirrors the property test's independent
re-derivation `(0..8).fold(0u64, |acc, i| acc | ((buf[i] as u64) << (8*i)))`.

`Array.getD … 0` keeps the oracle total without bounds arguments; every
theorem applies it under `8 ≤ buf.val.size`, so the accessed bytes are
exactly the real slice bytes. -/
private def leDecode (buf : RustSlice u8) : Nat :=
  (buf.val.getD 0 (0 : u8)).toNat
    + (buf.val.getD 1 (0 : u8)).toNat * 2 ^ 8
    + (buf.val.getD 2 (0 : u8)).toNat * 2 ^ 16
    + (buf.val.getD 3 (0 : u8)).toNat * 2 ^ 24
    + (buf.val.getD 4 (0 : u8)).toNat * 2 ^ 32
    + (buf.val.getD 5 (0 : u8)).toNat * 2 ^ 40
    + (buf.val.getD 6 (0 : u8)).toNat * 2 ^ 48
    + (buf.val.getD 7 (0 : u8)).toNat * 2 ^ 56

/-! ## Generic scaffolding (pattern reused from `big_endian_read_u64_into`,
`slice_get_u64`). -/

/-- `RustM.ok x >>= f = f x`. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- `RustM.fail e >>= f = RustM.fail e` — error short-circuits the bind. -/
@[simp]
private theorem RustM_fail_bind {α β : Type} (e : Error) (f : α → RustM β) :
    (RustM.fail e : RustM α) >>= f = RustM.fail e := rfl

/-- Indexing a slice in-bounds at a `Nat` literal index. -/
private theorem idx_ok (buf : RustSlice u8) (n : Nat) (k : usize)
    (hk : k.toNat = n) (h : n < buf.val.size) :
    (buf[k]_? : RustM u8) = RustM.ok (buf.val[n]'h) := by
  subst hk
  show (if h : k.toNat < buf.val.size then pure (buf.val[k])
          else .fail .arrayOutOfBounds) = RustM.ok (buf.val[k.toNat]'h)
  rw [dif_pos h]; rfl

/-- Indexing a slice out-of-bounds fails with `arrayOutOfBounds`. -/
private theorem idx_fail (buf : RustSlice u8) (n : Nat) (k : usize)
    (hk : k.toNat = n) (h : buf.val.size ≤ n) :
    (buf[k]_? : RustM u8) = RustM.fail Error.arrayOutOfBounds := by
  subst hk
  show (if h : k.toNat < buf.val.size then pure (buf.val[k])
          else .fail .arrayOutOfBounds) = RustM.fail Error.arrayOutOfBounds
  rw [dif_neg (by omega)]

/-- The widening `u8 → u64` cast. -/
private theorem cast_ok (b : u8) :
    (rust_primitives.hax.cast_op b : RustM u64) = RustM.ok (UInt8.toUInt64 b) := rfl

/-- Bitwise OR is total. -/
private theorem or_ok (a b : u64) :
    (a |||? b : RustM u64) = RustM.ok (a ||| b) := rfl

/-- Left-shift by a valid constant amount. -/
private theorem shl_ok (x : u64) (k : i32) (hk : (0 ≤ k && k < 64) = true) :
    (x <<<? k : RustM u64) = RustM.ok (x <<< (k.toNatClampNeg.toUInt64)) := by
  show (rust_primitives.ops.bit.Shl.shl x k : RustM u64) = _
  show (if (0 ≤ k && k < 64)
        then pure (x <<< (k.toNatClampNeg.toUInt64))
        else (.fail .integerOverflow : RustM u64)) = _
  rw [hk]; rfl

/-- `Array.getD` on an in-bounds index is `getElem`. -/
private theorem arr_getD (a : Array u8) (i : Nat) (h : i < a.size) :
    a.getD i (0 : u8) = a[i]'h := by
  simp [Array.getD, h]

/-! ## Little-endian byte-assembly form of `read_u64`.

`|||` is left-associative and binds looser than `<<<`, so `leExpr` is
exactly the left-nested OR the extracted code builds: `buf[0]` is the
*least* significant byte (no shift), `buf[7]` shifted by 56. -/

private def leExpr (b0 b1 b2 b3 b4 b5 b6 b7 : u8) : u64 :=
  UInt8.toUInt64 b0
    ||| UInt8.toUInt64 b1 <<< (8 : UInt64)
    ||| UInt8.toUInt64 b2 <<< (16 : UInt64)
    ||| UInt8.toUInt64 b3 <<< (24 : UInt64)
    ||| UInt8.toUInt64 b4 <<< (32 : UInt64)
    ||| UInt8.toUInt64 b5 <<< (40 : UInt64)
    ||| UInt8.toUInt64 b6 <<< (48 : UInt64)
    ||| UInt8.toUInt64 b7 <<< (56 : UInt64)

/-- Additive (disjoint-slot) normal form of the byte assembly, at the
    `BitVec 64` level. -/
private def leBV (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  (b0.setWidth 64)
    + ((b1.setWidth 64) <<< (8 : Nat))
    + ((b2.setWidth 64) <<< (16 : Nat))
    + ((b3.setWidth 64) <<< (24 : Nat))
    + ((b4.setWidth 64) <<< (32 : Nat))
    + ((b5.setWidth 64) <<< (40 : Nat))
    + ((b6.setWidth 64) <<< (48 : Nat))
    + ((b7.setWidth 64) <<< (56 : Nat))

/-- The eight byte slots are disjoint, so `|||` is `+`: a pure bitvector
    identity discharged by `bv_decide`. -/
private theorem leExpr_toBitVec (b0 b1 b2 b3 b4 b5 b6 b7 : u8) :
    (leExpr b0 b1 b2 b3 b4 b5 b6 b7).toBitVec
      = leBV b0.toBitVec b1.toBitVec b2.toBitVec b3.toBitVec
             b4.toBitVec b5.toBitVec b6.toBitVec b7.toBitVec := by
  unfold leExpr leBV
  bv_decide

/-- `.toNat` of the additive form distributes into the `leDecode`
    arithmetic (no `Nat.land` thanks to disjoint shifts). -/
private theorem leBV_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (leBV b0 b1 b2 b3 b4 b5 b6 b7).toNat
      = b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24
        + b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48
        + b7.toNat * 2 ^ 56 := by
  have h0 : b0.toNat < 2 ^ 8 := b0.isLt
  have h1 : b1.toNat < 2 ^ 8 := b1.isLt
  have h2 : b2.toNat < 2 ^ 8 := b2.isLt
  have h3 : b3.toNat < 2 ^ 8 := b3.isLt
  have h4 : b4.toNat < 2 ^ 8 := b4.isLt
  have h5 : b5.toNat < 2 ^ 8 := b5.isLt
  have h6 : b6.toNat < 2 ^ 8 := b6.isLt
  have h7 : b7.toNat < 2 ^ 8 := b7.isLt
  unfold leBV
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
             Nat.shiftLeft_eq]
  omega

private theorem leExpr_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : u8) :
    (leExpr b0 b1 b2 b3 b4 b5 b6 b7).toNat
      = b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24
        + b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48
        + b7.toNat * 2 ^ 56 := by
  have h := congrArg BitVec.toNat (leExpr_toBitVec b0 b1 b2 b3 b4 b5 b6 b7)
  rw [leBV_toNat] at h
  simpa using h

/-! ## Obligations. -/

/-- Postcondition (functional correctness): when `buf.len() ≥ 8`,
    `read_u64` completes successfully and the returned `u64`, read as a
    `Nat`, is the little-endian interpretation of the first 8 bytes of
    `buf` — `buf[0]` least significant, `buf[7]` most significant.

    Captures the property test `prop_little_endian_decode_of_first_8_bytes`
    (whose `expected` is the same byte/shift/OR re-derivation over indices
    `0..8`, with buffers of length `8..=64` also pinning down that bytes at
    index ≥ 8 are irrelevant). Subsumes the concrete unit tests
    `doctest_read_u64` (`1_000_000u64.to_le_bytes()` ↦ `1_000_000`) and
    `regression173_array_impl` (a 100-byte zero array ↦ `0`), which are
    instances of this clause. A big-endian, byte-swapped, wrong-width or
    chunk-misreading implementation falsifies it; the `∃ r, … = RustM.ok r`
    shape also certifies "no panic on valid input". -/
theorem read_u64_little_endian_decode
    (buf : RustSlice u8) (hlen : 8 ≤ buf.val.size) :
    ∃ r : u64,
      little_endian_read_u64.read_u64 buf = RustM.ok r ∧
      r.toNat = leDecode buf := by
  have h0 : 0 < buf.val.size := by omega
  have h1 : 1 < buf.val.size := by omega
  have h2 : 2 < buf.val.size := by omega
  have h3 : 3 < buf.val.size := by omega
  have h4 : 4 < buf.val.size := by omega
  have h5 : 5 < buf.val.size := by omega
  have h6 : 6 < buf.val.size := by omega
  have h7 : 7 < buf.val.size := by omega
  have hI0 := idx_ok buf 0 (0 : usize) (by decide) h0
  have hI1 := idx_ok buf 1 (1 : usize) (by decide) h1
  have hI2 := idx_ok buf 2 (2 : usize) (by decide) h2
  have hI3 := idx_ok buf 3 (3 : usize) (by decide) h3
  have hI4 := idx_ok buf 4 (4 : usize) (by decide) h4
  have hI5 := idx_ok buf 5 (5 : usize) (by decide) h5
  have hI6 := idx_ok buf 6 (6 : usize) (by decide) h6
  have hI7 := idx_ok buf 7 (7 : usize) (by decide) h7
  have hs8  : (0 ≤ (8 : i32) && (8 : i32) < 64) = true := by decide
  have hs16 : (0 ≤ (16 : i32) && (16 : i32) < 64) = true := by decide
  have hs24 : (0 ≤ (24 : i32) && (24 : i32) < 64) = true := by decide
  have hs32 : (0 ≤ (32 : i32) && (32 : i32) < 64) = true := by decide
  have hs40 : (0 ≤ (40 : i32) && (40 : i32) < 64) = true := by decide
  have hs48 : (0 ≤ (48 : i32) && (48 : i32) < 64) = true := by decide
  have hs56 : (0 ≤ (56 : i32) && (56 : i32) < 64) = true := by decide
  have e8  : ((8 : i32).toNatClampNeg).toUInt64 = (8 : UInt64) := by decide
  have e16 : ((16 : i32).toNatClampNeg).toUInt64 = (16 : UInt64) := by decide
  have e24 : ((24 : i32).toNatClampNeg).toUInt64 = (24 : UInt64) := by decide
  have e32 : ((32 : i32).toNatClampNeg).toUInt64 = (32 : UInt64) := by decide
  have e40 : ((40 : i32).toNatClampNeg).toUInt64 = (40 : UInt64) := by decide
  have e48 : ((48 : i32).toNatClampNeg).toUInt64 = (48 : UInt64) := by decide
  have e56 : ((56 : i32).toNatClampNeg).toUInt64 = (56 : UInt64) := by decide
  refine ⟨leExpr (buf.val[0]'h0) (buf.val[1]'h1) (buf.val[2]'h2)
            (buf.val[3]'h3) (buf.val[4]'h4) (buf.val[5]'h5)
            (buf.val[6]'h6) (buf.val[7]'h7), ?_, ?_⟩
  · simp only [little_endian_read_u64.read_u64,
               hI0, hI1, hI2, hI3, hI4, hI5, hI6, hI7, cast_ok,
               shl_ok _ (8 : i32) hs8, shl_ok _ (16 : i32) hs16,
               shl_ok _ (24 : i32) hs24, shl_ok _ (32 : i32) hs32,
               shl_ok _ (40 : i32) hs40, shl_ok _ (48 : i32) hs48,
               shl_ok _ (56 : i32) hs56,
               e8, e16, e24, e32, e40, e48, e56,
               or_ok, leExpr, RustM_ok_bind]
  · rw [leExpr_toNat]
    unfold leDecode
    simp only [arr_getD buf.val 0 h0, arr_getD buf.val 1 h1,
        arr_getD buf.val 2 h2, arr_getD buf.val 3 h3,
        arr_getD buf.val 4 h4, arr_getD buf.val 5 h5,
        arr_getD buf.val 6 h6, arr_getD buf.val 7 h7]

/-- Failure condition (documented `# Panics` clause / precondition
    `buf.len() ≥ 8`): when `buf.len() < 8`, `read_u64` does not return a
    value — it fails with an out-of-bounds array access (the modeled form
    of the original index panic). The reads run left-to-right over indices
    `0..8`, so the first index `≥ buf.len()` (namely `buf.len()` itself,
    which is `< 8`) trips the partial slice operator and short-circuits the
    `RustM` computation to `.fail .arrayOutOfBounds`.

    Captures the property test `prop_panics_when_buffer_too_short` (every
    short length `0..=7`, arbitrary contents) and the concrete
    `#[should_panic]` unit test `small_u64_read_little_endian` (length 7),
    an instance of this clause. -/
theorem read_u64_short_buffer_fails
    (buf : RustSlice u8) (hlen : buf.val.size < 8) :
    little_endian_read_u64.read_u64 buf = RustM.fail Error.arrayOutOfBounds := by
  have hs8  : (0 ≤ (8 : i32) && (8 : i32) < 64) = true := by decide
  have hs16 : (0 ≤ (16 : i32) && (16 : i32) < 64) = true := by decide
  have hs24 : (0 ≤ (24 : i32) && (24 : i32) < 64) = true := by decide
  have hs32 : (0 ≤ (32 : i32) && (32 : i32) < 64) = true := by decide
  have hs40 : (0 ≤ (40 : i32) && (40 : i32) < 64) = true := by decide
  have hs48 : (0 ≤ (48 : i32) && (48 : i32) < 64) = true := by decide
  have hs56 : (0 ≤ (56 : i32) && (56 : i32) < 64) = true := by decide
  have hcases : buf.val.size = 0 ∨ buf.val.size = 1 ∨ buf.val.size = 2 ∨
                buf.val.size = 3 ∨ buf.val.size = 4 ∨ buf.val.size = 5 ∨
                buf.val.size = 6 ∨ buf.val.size = 7 := by omega
  rcases hcases with h|h|h|h|h|h|h|h
  · have hf := idx_fail buf 0 (0 : usize) (by decide) (by omega)
    simp only [little_endian_read_u64.read_u64, hf, RustM_fail_bind]
  · have hI0 := idx_ok buf 0 (0 : usize) (by decide) (by omega)
    have hf := idx_fail buf 1 (1 : usize) (by decide) (by omega)
    simp only [little_endian_read_u64.read_u64, hI0, hf, cast_ok,
               shl_ok _ (8 : i32) hs8, or_ok, RustM_ok_bind, RustM_fail_bind]
  · have hI0 := idx_ok buf 0 (0 : usize) (by decide) (by omega)
    have hI1 := idx_ok buf 1 (1 : usize) (by decide) (by omega)
    have hf := idx_fail buf 2 (2 : usize) (by decide) (by omega)
    simp only [little_endian_read_u64.read_u64, hI0, hI1, hf, cast_ok,
               shl_ok _ (8 : i32) hs8, shl_ok _ (16 : i32) hs16,
               or_ok, RustM_ok_bind, RustM_fail_bind]
  · have hI0 := idx_ok buf 0 (0 : usize) (by decide) (by omega)
    have hI1 := idx_ok buf 1 (1 : usize) (by decide) (by omega)
    have hI2 := idx_ok buf 2 (2 : usize) (by decide) (by omega)
    have hf := idx_fail buf 3 (3 : usize) (by decide) (by omega)
    simp only [little_endian_read_u64.read_u64, hI0, hI1, hI2, hf, cast_ok,
               shl_ok _ (8 : i32) hs8, shl_ok _ (16 : i32) hs16,
               shl_ok _ (24 : i32) hs24, or_ok, RustM_ok_bind, RustM_fail_bind]
  · have hI0 := idx_ok buf 0 (0 : usize) (by decide) (by omega)
    have hI1 := idx_ok buf 1 (1 : usize) (by decide) (by omega)
    have hI2 := idx_ok buf 2 (2 : usize) (by decide) (by omega)
    have hI3 := idx_ok buf 3 (3 : usize) (by decide) (by omega)
    have hf := idx_fail buf 4 (4 : usize) (by decide) (by omega)
    simp only [little_endian_read_u64.read_u64, hI0, hI1, hI2, hI3, hf, cast_ok,
               shl_ok _ (8 : i32) hs8, shl_ok _ (16 : i32) hs16,
               shl_ok _ (24 : i32) hs24, shl_ok _ (32 : i32) hs32,
               or_ok, RustM_ok_bind, RustM_fail_bind]
  · have hI0 := idx_ok buf 0 (0 : usize) (by decide) (by omega)
    have hI1 := idx_ok buf 1 (1 : usize) (by decide) (by omega)
    have hI2 := idx_ok buf 2 (2 : usize) (by decide) (by omega)
    have hI3 := idx_ok buf 3 (3 : usize) (by decide) (by omega)
    have hI4 := idx_ok buf 4 (4 : usize) (by decide) (by omega)
    have hf := idx_fail buf 5 (5 : usize) (by decide) (by omega)
    simp only [little_endian_read_u64.read_u64, hI0, hI1, hI2, hI3, hI4, hf,
               cast_ok, shl_ok _ (8 : i32) hs8, shl_ok _ (16 : i32) hs16,
               shl_ok _ (24 : i32) hs24, shl_ok _ (32 : i32) hs32,
               shl_ok _ (40 : i32) hs40, or_ok, RustM_ok_bind, RustM_fail_bind]
  · have hI0 := idx_ok buf 0 (0 : usize) (by decide) (by omega)
    have hI1 := idx_ok buf 1 (1 : usize) (by decide) (by omega)
    have hI2 := idx_ok buf 2 (2 : usize) (by decide) (by omega)
    have hI3 := idx_ok buf 3 (3 : usize) (by decide) (by omega)
    have hI4 := idx_ok buf 4 (4 : usize) (by decide) (by omega)
    have hI5 := idx_ok buf 5 (5 : usize) (by decide) (by omega)
    have hf := idx_fail buf 6 (6 : usize) (by decide) (by omega)
    simp only [little_endian_read_u64.read_u64, hI0, hI1, hI2, hI3, hI4, hI5,
               hf, cast_ok, shl_ok _ (8 : i32) hs8, shl_ok _ (16 : i32) hs16,
               shl_ok _ (24 : i32) hs24, shl_ok _ (32 : i32) hs32,
               shl_ok _ (40 : i32) hs40, shl_ok _ (48 : i32) hs48,
               or_ok, RustM_ok_bind, RustM_fail_bind]
  · have hI0 := idx_ok buf 0 (0 : usize) (by decide) (by omega)
    have hI1 := idx_ok buf 1 (1 : usize) (by decide) (by omega)
    have hI2 := idx_ok buf 2 (2 : usize) (by decide) (by omega)
    have hI3 := idx_ok buf 3 (3 : usize) (by decide) (by omega)
    have hI4 := idx_ok buf 4 (4 : usize) (by decide) (by omega)
    have hI5 := idx_ok buf 5 (5 : usize) (by decide) (by omega)
    have hI6 := idx_ok buf 6 (6 : usize) (by decide) (by omega)
    have hf := idx_fail buf 7 (7 : usize) (by decide) (by omega)
    simp only [little_endian_read_u64.read_u64, hI0, hI1, hI2, hI3, hI4, hI5,
               hI6, hf, cast_ok, shl_ok _ (8 : i32) hs8,
               shl_ok _ (16 : i32) hs16, shl_ok _ (24 : i32) hs24,
               shl_ok _ (32 : i32) hs32, shl_ok _ (40 : i32) hs40,
               shl_ok _ (48 : i32) hs48, shl_ok _ (56 : i32) hs56,
               or_ok, RustM_ok_bind, RustM_fail_bind]

end Little_endian_read_u64Obligations
