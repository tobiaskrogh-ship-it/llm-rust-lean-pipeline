-- Companion obligations file for the `big_endian_read_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import big_endian_read_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Big_endian_read_u64Obligations

/-! ## Specification oracle: big-endian decoding of the first eight bytes.

Independent `Nat`-level reference for the big-endian value built from
exactly the first eight bytes of `buf`: byte 0 is the most significant
(`* 2^56`), byte 7 the least significant (`* 2^0`). This mirrors the
Rust property test's `be_first_eight` helper

    let mut acc = 0; for i in 0..8 { acc = (acc << 8) | buf[i] as u64 }

without restating the implementation's shift/or form. `Array.getD … 0`
makes the oracle total; only indices `0 … 7` are ever referenced, so the
spec is, by construction, independent of `buf.len()` beyond the first
eight bytes (this is what pins down the "trailing bytes are ignored"
sub-claim). The maximum value is `255 * 2^56 + … + 255 = 2^64 - 1`, so
`UInt64.ofNat` of it is exact. -/
private def beFirstEight (buf : RustSlice u8) : Nat :=
  (buf.val.getD 0 0).toNat * 2 ^ 56
    + (buf.val.getD 1 0).toNat * 2 ^ 48
    + (buf.val.getD 2 0).toNat * 2 ^ 40
    + (buf.val.getD 3 0).toNat * 2 ^ 32
    + (buf.val.getD 4 0).toNat * 2 ^ 24
    + (buf.val.getD 5 0).toNat * 2 ^ 16
    + (buf.val.getD 6 0).toNat * 2 ^ 8
    + (buf.val.getD 7 0).toNat

/-! ## Generic helpers. -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- `RustM.fail e >>= f = RustM.fail e`. Once any read is out of bounds the
    monadic bind short-circuits; this collapses the entire tail. -/
@[simp]
private theorem RustM_fail_bind {α β : Type} (e : Error) (f : α → RustM β) :
    RustM.fail e >>= f = RustM.fail e := rfl

/-- In-bounds `Array.getD` collapses to the underlying element. Bridges the
    `getD`-based oracle `beFirstEight` to the concrete element reads the
    implementation performs. -/
private theorem array_getD_eq (a : Array u8) (k : Nat) (hk : k < a.size) :
    a.getD k 0 = a[k]'hk := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]

/-! ## Per-index discharge of the partial slice operator `buf[k]_?`.

The `usize.instGetElemResultSeq` instance reduces `buf[k]_?` to
`dite (k.toNat < buf.val.size) (pure …) (fail …)`. Each helper packages
the `dif_pos`/`dif_neg` discharge together with the `(k : usize).toNat = k`
definitional reduction, so callers only deal with plain `Nat` bounds.
Pattern from `slice_get_u64` / `clever_000_has_close_elements`. -/

private theorem idx0_ok (buf : RustSlice u8) (h : 0 < buf.val.size) :
    (buf[(0 : usize)]_? : RustM u8) = pure (buf.val[0]'h) := by
  have hb : USize64.toNat (0 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (0 : usize) < buf.val.size
          then pure (buf.val[(0 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = pure (buf.val[0]'h)
  rw [dif_pos hb] <;> rfl

private theorem idx1_ok (buf : RustSlice u8) (h : 1 < buf.val.size) :
    (buf[(1 : usize)]_? : RustM u8) = pure (buf.val[1]'h) := by
  have hb : USize64.toNat (1 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (1 : usize) < buf.val.size
          then pure (buf.val[(1 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = pure (buf.val[1]'h)
  rw [dif_pos hb] <;> rfl

private theorem idx2_ok (buf : RustSlice u8) (h : 2 < buf.val.size) :
    (buf[(2 : usize)]_? : RustM u8) = pure (buf.val[2]'h) := by
  have hb : USize64.toNat (2 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (2 : usize) < buf.val.size
          then pure (buf.val[(2 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = pure (buf.val[2]'h)
  rw [dif_pos hb] <;> rfl

private theorem idx3_ok (buf : RustSlice u8) (h : 3 < buf.val.size) :
    (buf[(3 : usize)]_? : RustM u8) = pure (buf.val[3]'h) := by
  have hb : USize64.toNat (3 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (3 : usize) < buf.val.size
          then pure (buf.val[(3 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = pure (buf.val[3]'h)
  rw [dif_pos hb] <;> rfl

private theorem idx4_ok (buf : RustSlice u8) (h : 4 < buf.val.size) :
    (buf[(4 : usize)]_? : RustM u8) = pure (buf.val[4]'h) := by
  have hb : USize64.toNat (4 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (4 : usize) < buf.val.size
          then pure (buf.val[(4 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = pure (buf.val[4]'h)
  rw [dif_pos hb] <;> rfl

private theorem idx5_ok (buf : RustSlice u8) (h : 5 < buf.val.size) :
    (buf[(5 : usize)]_? : RustM u8) = pure (buf.val[5]'h) := by
  have hb : USize64.toNat (5 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (5 : usize) < buf.val.size
          then pure (buf.val[(5 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = pure (buf.val[5]'h)
  rw [dif_pos hb] <;> rfl

private theorem idx6_ok (buf : RustSlice u8) (h : 6 < buf.val.size) :
    (buf[(6 : usize)]_? : RustM u8) = pure (buf.val[6]'h) := by
  have hb : USize64.toNat (6 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (6 : usize) < buf.val.size
          then pure (buf.val[(6 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = pure (buf.val[6]'h)
  rw [dif_pos hb] <;> rfl

private theorem idx7_ok (buf : RustSlice u8) (h : 7 < buf.val.size) :
    (buf[(7 : usize)]_? : RustM u8) = pure (buf.val[7]'h) := by
  have hb : USize64.toNat (7 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (7 : usize) < buf.val.size
          then pure (buf.val[(7 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = pure (buf.val[7]'h)
  rw [dif_pos hb] <;> rfl

private theorem idx0_fail (buf : RustSlice u8) (h : ¬ 0 < buf.val.size) :
    (buf[(0 : usize)]_? : RustM u8) = RustM.fail .arrayOutOfBounds := by
  have hb : ¬ USize64.toNat (0 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (0 : usize) < buf.val.size
          then pure (buf.val[(0 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = RustM.fail .arrayOutOfBounds
  rw [dif_neg hb]

private theorem idx1_fail (buf : RustSlice u8) (h : ¬ 1 < buf.val.size) :
    (buf[(1 : usize)]_? : RustM u8) = RustM.fail .arrayOutOfBounds := by
  have hb : ¬ USize64.toNat (1 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (1 : usize) < buf.val.size
          then pure (buf.val[(1 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = RustM.fail .arrayOutOfBounds
  rw [dif_neg hb]

private theorem idx2_fail (buf : RustSlice u8) (h : ¬ 2 < buf.val.size) :
    (buf[(2 : usize)]_? : RustM u8) = RustM.fail .arrayOutOfBounds := by
  have hb : ¬ USize64.toNat (2 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (2 : usize) < buf.val.size
          then pure (buf.val[(2 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = RustM.fail .arrayOutOfBounds
  rw [dif_neg hb]

private theorem idx3_fail (buf : RustSlice u8) (h : ¬ 3 < buf.val.size) :
    (buf[(3 : usize)]_? : RustM u8) = RustM.fail .arrayOutOfBounds := by
  have hb : ¬ USize64.toNat (3 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (3 : usize) < buf.val.size
          then pure (buf.val[(3 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = RustM.fail .arrayOutOfBounds
  rw [dif_neg hb]

private theorem idx4_fail (buf : RustSlice u8) (h : ¬ 4 < buf.val.size) :
    (buf[(4 : usize)]_? : RustM u8) = RustM.fail .arrayOutOfBounds := by
  have hb : ¬ USize64.toNat (4 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (4 : usize) < buf.val.size
          then pure (buf.val[(4 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = RustM.fail .arrayOutOfBounds
  rw [dif_neg hb]

private theorem idx5_fail (buf : RustSlice u8) (h : ¬ 5 < buf.val.size) :
    (buf[(5 : usize)]_? : RustM u8) = RustM.fail .arrayOutOfBounds := by
  have hb : ¬ USize64.toNat (5 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (5 : usize) < buf.val.size
          then pure (buf.val[(5 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = RustM.fail .arrayOutOfBounds
  rw [dif_neg hb]

private theorem idx6_fail (buf : RustSlice u8) (h : ¬ 6 < buf.val.size) :
    (buf[(6 : usize)]_? : RustM u8) = RustM.fail .arrayOutOfBounds := by
  have hb : ¬ USize64.toNat (6 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (6 : usize) < buf.val.size
          then pure (buf.val[(6 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = RustM.fail .arrayOutOfBounds
  rw [dif_neg hb]

private theorem idx7_fail (buf : RustSlice u8) (h : ¬ 7 < buf.val.size) :
    (buf[(7 : usize)]_? : RustM u8) = RustM.fail .arrayOutOfBounds := by
  have hb : ¬ USize64.toNat (7 : usize) < buf.val.size := h
  show (if hh : USize64.toNat (7 : usize) < buf.val.size
          then pure (buf.val[(7 : usize)])
          else (.fail .arrayOutOfBounds : RustM u8)) = RustM.fail .arrayOutOfBounds
  rw [dif_neg hb]

/-! ## The assembled `u64` value.

`read_u64` widens each of the first eight bytes to `u64`, shifts byte `k`
left by `8 * (7 - k)` bits, and ORs them together (byte 0 most
significant, byte 7 unshifted). `assembleExpr` is exactly that
OR-of-shifts, in the bytes; `bvAssemble` is the *additive* `BitVec 64`
normal form (the eight byte slots are disjoint, so `|||` = `+`). This is
the same recipe as `big_endian_from_slice_u64`'s
`swapExpr`/`bvRev`/`swapExpr_toNat` chain. -/

private def assembleExpr (c0 c1 c2 c3 c4 c5 c6 c7 : u8) : u64 :=
  ((((((((c0.toUInt64 <<< (56 : UInt64))
    ||| (c1.toUInt64 <<< (48 : UInt64)))
    ||| (c2.toUInt64 <<< (40 : UInt64)))
    ||| (c3.toUInt64 <<< (32 : UInt64)))
    ||| (c4.toUInt64 <<< (24 : UInt64)))
    ||| (c5.toUInt64 <<< (16 : UInt64)))
    ||| (c6.toUInt64 <<< (8 : UInt64)))
    ||| c7.toUInt64)

private def bvAssemble (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 8) : BitVec 64 :=
  ((a0.setWidth 64) <<< (56 : Nat))
    + ((a1.setWidth 64) <<< (48 : Nat))
    + ((a2.setWidth 64) <<< (40 : Nat))
    + ((a3.setWidth 64) <<< (32 : Nat))
    + ((a4.setWidth 64) <<< (24 : Nat))
    + ((a5.setWidth 64) <<< (16 : Nat))
    + ((a6.setWidth 64) <<< (8 : Nat))
    + (a7.setWidth 64)

/-- The OR/shift form equals the additive form (pure bitvector identity:
    disjoint byte slots). Discharged by `bv_decide`, exactly as
    `big_endian_from_slice_u64`'s `swapExpr_toBitVec`. -/
private theorem assembleExpr_toBitVec (c0 c1 c2 c3 c4 c5 c6 c7 : u8) :
    (assembleExpr c0 c1 c2 c3 c4 c5 c6 c7).toBitVec
      = bvAssemble c0.toBitVec c1.toBitVec c2.toBitVec c3.toBitVec
                   c4.toBitVec c5.toBitVec c6.toBitVec c7.toBitVec := by
  unfold assembleExpr bvAssemble
  bv_decide

/-- `bvAssemble` at the `Nat` level is the big-endian byte sum. After
    pushing `BitVec.toNat` through the additive form (no `Nat.lor` thanks
    to `+`), the residual is Presburger and `omega` closes it. Mirrors
    `big_endian_from_slice_u64`'s `bvRev_toNat`. -/
private theorem bvAssemble_toNat (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 8) :
    (bvAssemble a0 a1 a2 a3 a4 a5 a6 a7).toNat
      = a0.toNat * 2 ^ 56 + a1.toNat * 2 ^ 48 + a2.toNat * 2 ^ 40
        + a3.toNat * 2 ^ 32 + a4.toNat * 2 ^ 24 + a5.toNat * 2 ^ 16
        + a6.toNat * 2 ^ 8 + a7.toNat := by
  have h0 := a0.isLt
  have h1 := a1.isLt
  have h2 := a2.isLt
  have h3 := a3.isLt
  have h4 := a4.isLt
  have h5 := a5.isLt
  have h6 := a6.isLt
  have h7 := a7.isLt
  unfold bvAssemble
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
             Nat.shiftLeft_eq]
  omega

private theorem assembleExpr_toNat (c0 c1 c2 c3 c4 c5 c6 c7 : u8) :
    (assembleExpr c0 c1 c2 c3 c4 c5 c6 c7).toNat
      = c0.toNat * 2 ^ 56 + c1.toNat * 2 ^ 48 + c2.toNat * 2 ^ 40
        + c3.toNat * 2 ^ 32 + c4.toNat * 2 ^ 24 + c5.toNat * 2 ^ 16
        + c6.toNat * 2 ^ 8 + c7.toNat := by
  have hbv := congrArg BitVec.toNat
    (assembleExpr_toBitVec c0 c1 c2 c3 c4 c5 c6 c7)
  rw [bvAssemble_toNat] at hbv
  simpa using hbv

/-! ## Reduction of the monadic body when `buf.len() ≥ 8`.

Each `buf[k]_?` succeeds (`idx*_ok`), `cast_op` is the `u8 → u64`
widening, `<<<?` is the static in-range shift (always succeeds), `|||?`
is total. The whole `do` block collapses to `RustM.ok` of the
OR-of-shifts. Pattern reused from `slice_get_u64` (index discharge) and
`average_floor_u64` (`<<<?`/`>>>?` instance + `if`-collapse). -/
private theorem read_u64_reduce (buf : RustSlice u8)
    (h0 : 0 < buf.val.size) (h1 : 1 < buf.val.size) (h2 : 2 < buf.val.size)
    (h3 : 3 < buf.val.size) (h4 : 4 < buf.val.size) (h5 : 5 < buf.val.size)
    (h6 : 6 < buf.val.size) (h7 : 7 < buf.val.size) :
    big_endian_read_u64.read_u64 buf
      = RustM.ok (assembleExpr (buf.val[0]'h0) (buf.val[1]'h1)
          (buf.val[2]'h2) (buf.val[3]'h3) (buf.val[4]'h4) (buf.val[5]'h5)
          (buf.val[6]'h6) (buf.val[7]'h7)) := by
  simp only [big_endian_read_u64.read_u64,
             idx0_ok buf h0, idx1_ok buf h1, idx2_ok buf h2, idx3_ok buf h3,
             idx4_ok buf h4, idx5_ok buf h5, idx6_ok buf h6, idx7_ok buf h7,
             rust_primitives.hax.cast_op, Cast.cast,
             rust_primitives.ops.bit.Shl.shl, pure_bind]
  simp only [show ((0 : Int32) ≤ (56 : Int32) && (56 : Int32) < 64) = true from rfl,
             show ((0 : Int32) ≤ (48 : Int32) && (48 : Int32) < 64) = true from rfl,
             show ((0 : Int32) ≤ (40 : Int32) && (40 : Int32) < 64) = true from rfl,
             show ((0 : Int32) ≤ (32 : Int32) && (32 : Int32) < 64) = true from rfl,
             show ((0 : Int32) ≤ (24 : Int32) && (24 : Int32) < 64) = true from rfl,
             show ((0 : Int32) ≤ (16 : Int32) && (16 : Int32) < 64) = true from rfl,
             show ((0 : Int32) ≤ (8 : Int32) && (8 : Int32) < 64) = true from rfl,
             ↓reduceIte, pure_bind]
  rw [show ((56 : Int32).toNatClampNeg.toUInt64) = (56 : UInt64) from rfl,
      show ((48 : Int32).toNatClampNeg.toUInt64) = (48 : UInt64) from rfl,
      show ((40 : Int32).toNatClampNeg.toUInt64) = (40 : UInt64) from rfl,
      show ((32 : Int32).toNatClampNeg.toUInt64) = (32 : UInt64) from rfl,
      show ((24 : Int32).toNatClampNeg.toUInt64) = (24 : UInt64) from rfl,
      show ((16 : Int32).toNatClampNeg.toUInt64) = (16 : UInt64) from rfl,
      show ((8 : Int32).toNatClampNeg.toUInt64) = (8 : UInt64) from rfl]
  rfl

/-- Postcondition (functional correctness). Captures the property test
    `postcondition_big_endian_of_first_eight_bytes`: for every buffer of
    length ≥ 8, `read_u64` returns the big-endian value assembled from
    exactly the first eight bytes, in order (`buf[0]` most significant …
    `buf[7]` least significant). The single equation simultaneously pins
    down *which* bytes are read (the first eight), the *byte order*
    (big-endian — a little-endian or byte-swapped implementation would
    falsify it on the structured single-byte cases), and that bytes at
    index ≥ 8 do not affect the result (`beFirstEight` references only
    indices 0…7, and the equation is stated for arbitrary length ≥ 8). -/
theorem read_u64_postcondition (buf : RustSlice u8) (h : 8 ≤ buf.val.size) :
    big_endian_read_u64.read_u64 buf = RustM.ok (UInt64.ofNat (beFirstEight buf)) := by
  have h0 : 0 < buf.val.size := by omega
  have h1 : 1 < buf.val.size := by omega
  have h2 : 2 < buf.val.size := by omega
  have h3 : 3 < buf.val.size := by omega
  have h4 : 4 < buf.val.size := by omega
  have h5 : 5 < buf.val.size := by omega
  have h6 : 6 < buf.val.size := by omega
  have h7 : 7 < buf.val.size := by omega
  rw [read_u64_reduce buf h0 h1 h2 h3 h4 h5 h6 h7]
  congr 1
  apply UInt64.toNat.inj
  rw [assembleExpr_toNat]
  have hbe : beFirstEight buf
      = (buf.val[0]'h0).toNat * 2 ^ 56 + (buf.val[1]'h1).toNat * 2 ^ 48
        + (buf.val[2]'h2).toNat * 2 ^ 40 + (buf.val[3]'h3).toNat * 2 ^ 32
        + (buf.val[4]'h4).toNat * 2 ^ 24 + (buf.val[5]'h5).toNat * 2 ^ 16
        + (buf.val[6]'h6).toNat * 2 ^ 8 + (buf.val[7]'h7).toNat := by
    unfold beFirstEight
    rw [array_getD_eq buf.val 0 h0, array_getD_eq buf.val 1 h1,
        array_getD_eq buf.val 2 h2, array_getD_eq buf.val 3 h3,
        array_getD_eq buf.val 4 h4, array_getD_eq buf.val 5 h5,
        array_getD_eq buf.val 6 h6, array_getD_eq buf.val 7 h7]
  rw [hbe]
  have hb0 := (buf.val[0]'h0).toNat_lt
  have hb1 := (buf.val[1]'h1).toNat_lt
  have hb2 := (buf.val[2]'h2).toNat_lt
  have hb3 := (buf.val[3]'h3).toNat_lt
  have hb4 := (buf.val[4]'h4).toNat_lt
  have hb5 := (buf.val[5]'h5).toNat_lt
  have hb6 := (buf.val[6]'h6).toNat_lt
  have hb7 := (buf.val[7]'h7).toNat_lt
  have hsize : (UInt64.size : Nat) = 2 ^ 64 := rfl
  rw [UInt64.toNat_ofNat_of_lt' (by rw [hsize]; omega)]

/-- Failure condition. Captures the panicking half of the property test
    `panics_iff_buffer_shorter_than_eight`: for every buffer strictly
    shorter than eight bytes (lengths 0 … 7), `read_u64` panics. The
    single-element partial index operator `buf[i]_?` fails with
    `arrayOutOfBounds` at the first out-of-bounds read (index
    `buf.val.size`), and the monadic bind propagates that failure, so the
    whole computation reduces to `RustM.fail arrayOutOfBounds`. A buggy
    implementation slicing a shorter prefix (e.g. `buf[..4]`) would
    survive some short buffers and falsify this. -/
theorem read_u64_panics_when_short (buf : RustSlice u8) (h : buf.val.size < 8) :
    big_endian_read_u64.read_u64 buf = RustM.fail .arrayOutOfBounds := by
  -- The first out-of-bounds index is `buf.val.size` itself; reads
  -- `0 … size-1` succeed (`idx*_ok`), read `size` fails (`idx*_fail`),
  -- and `RustM_fail_bind` propagates the failure through the whole tail.
  have hcases : buf.val.size = 0 ∨ buf.val.size = 1 ∨ buf.val.size = 2
      ∨ buf.val.size = 3 ∨ buf.val.size = 4 ∨ buf.val.size = 5
      ∨ buf.val.size = 6 ∨ buf.val.size = 7 := by omega
  rcases hcases with hs|hs|hs|hs|hs|hs|hs|hs
  · simp only [big_endian_read_u64.read_u64,
               idx0_fail buf (by rw [hs]; omega),
               rust_primitives.hax.cast_op, Cast.cast,
               rust_primitives.ops.bit.Shl.shl,
               ↓reduceIte, pure_bind, RustM_ok_bind, RustM_fail_bind]
  · simp only [big_endian_read_u64.read_u64,
               idx0_ok buf (by omega), idx1_fail buf (by rw [hs]; omega),
               rust_primitives.hax.cast_op, Cast.cast,
               rust_primitives.ops.bit.Shl.shl,
               show ((0 : Int32) ≤ (56 : Int32) && (56 : Int32) < 64) = true from rfl,
               ↓reduceIte, pure_bind, RustM_ok_bind, RustM_fail_bind]
  · simp only [big_endian_read_u64.read_u64,
               idx0_ok buf (by omega), idx1_ok buf (by omega),
               idx2_fail buf (by rw [hs]; omega),
               rust_primitives.hax.cast_op, Cast.cast,
               rust_primitives.ops.bit.Shl.shl,
               show ((0 : Int32) ≤ (56 : Int32) && (56 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (48 : Int32) && (48 : Int32) < 64) = true from rfl,
               ↓reduceIte, pure_bind, RustM_ok_bind, RustM_fail_bind]
  · simp only [big_endian_read_u64.read_u64,
               idx0_ok buf (by omega), idx1_ok buf (by omega),
               idx2_ok buf (by omega), idx3_fail buf (by rw [hs]; omega),
               rust_primitives.hax.cast_op, Cast.cast,
               rust_primitives.ops.bit.Shl.shl,
               show ((0 : Int32) ≤ (56 : Int32) && (56 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (48 : Int32) && (48 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (40 : Int32) && (40 : Int32) < 64) = true from rfl,
               ↓reduceIte, pure_bind, RustM_ok_bind, RustM_fail_bind]
  · simp only [big_endian_read_u64.read_u64,
               idx0_ok buf (by omega), idx1_ok buf (by omega),
               idx2_ok buf (by omega), idx3_ok buf (by omega),
               idx4_fail buf (by rw [hs]; omega),
               rust_primitives.hax.cast_op, Cast.cast,
               rust_primitives.ops.bit.Shl.shl,
               show ((0 : Int32) ≤ (56 : Int32) && (56 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (48 : Int32) && (48 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (40 : Int32) && (40 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (32 : Int32) && (32 : Int32) < 64) = true from rfl,
               ↓reduceIte, pure_bind, RustM_ok_bind, RustM_fail_bind]
  · simp only [big_endian_read_u64.read_u64,
               idx0_ok buf (by omega), idx1_ok buf (by omega),
               idx2_ok buf (by omega), idx3_ok buf (by omega),
               idx4_ok buf (by omega), idx5_fail buf (by rw [hs]; omega),
               rust_primitives.hax.cast_op, Cast.cast,
               rust_primitives.ops.bit.Shl.shl,
               show ((0 : Int32) ≤ (56 : Int32) && (56 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (48 : Int32) && (48 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (40 : Int32) && (40 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (32 : Int32) && (32 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (24 : Int32) && (24 : Int32) < 64) = true from rfl,
               ↓reduceIte, pure_bind, RustM_ok_bind, RustM_fail_bind]
  · simp only [big_endian_read_u64.read_u64,
               idx0_ok buf (by omega), idx1_ok buf (by omega),
               idx2_ok buf (by omega), idx3_ok buf (by omega),
               idx4_ok buf (by omega), idx5_ok buf (by omega),
               idx6_fail buf (by rw [hs]; omega),
               rust_primitives.hax.cast_op, Cast.cast,
               rust_primitives.ops.bit.Shl.shl,
               show ((0 : Int32) ≤ (56 : Int32) && (56 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (48 : Int32) && (48 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (40 : Int32) && (40 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (32 : Int32) && (32 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (24 : Int32) && (24 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (16 : Int32) && (16 : Int32) < 64) = true from rfl,
               ↓reduceIte, pure_bind, RustM_ok_bind, RustM_fail_bind]
  · simp only [big_endian_read_u64.read_u64,
               idx0_ok buf (by omega), idx1_ok buf (by omega),
               idx2_ok buf (by omega), idx3_ok buf (by omega),
               idx4_ok buf (by omega), idx5_ok buf (by omega),
               idx6_ok buf (by omega), idx7_fail buf (by rw [hs]; omega),
               rust_primitives.hax.cast_op, Cast.cast,
               rust_primitives.ops.bit.Shl.shl,
               show ((0 : Int32) ≤ (56 : Int32) && (56 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (48 : Int32) && (48 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (40 : Int32) && (40 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (32 : Int32) && (32 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (24 : Int32) && (24 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (16 : Int32) && (16 : Int32) < 64) = true from rfl,
               show ((0 : Int32) ≤ (8 : Int32) && (8 : Int32) < 64) = true from rfl,
               ↓reduceIte, pure_bind, RustM_ok_bind, RustM_fail_bind]

/-- Precondition exactness / no-panic at the boundary. Captures the
    non-panicking half of `panics_iff_buffer_shorter_than_eight` ("length
    exactly 8 must not panic"), stated in its general form: for *every*
    buffer of length ≥ 8 the function completes successfully. Together
    with `read_u64_panics_when_short` this fixes the precondition exactly
    at `buf.len() ≥ 8`. -/
theorem read_u64_total_when_at_least_eight (buf : RustSlice u8)
    (h : 8 ≤ buf.val.size) :
    ∃ v : u64, big_endian_read_u64.read_u64 buf = RustM.ok v :=
  ⟨UInt64.ofNat (beFirstEight buf), read_u64_postcondition buf h⟩

end Big_endian_read_u64Obligations
