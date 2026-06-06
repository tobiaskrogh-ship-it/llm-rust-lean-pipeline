-- Companion obligations file for the `little_endian_read_u64_into` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import little_endian_read_u64_into

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

namespace Little_endian_read_u64_intoObligations

/-! ## Specification oracle: little-endian decode of an 8-byte window.

`leDecode src base` is the `Nat` value of the 8 bytes
`src[base], src[base+1], …, src[base+7]` read **little-endian**: the byte
at the *lowest* index (`base`) is the *least* significant. This is
expressed at the `Nat` level, independent of the implementation's
cast/shift/OR form, so the postcondition is a genuine semantic
specification rather than a restatement of the code. It matches the
property test's hand-written oracle exactly:
`expected |= (src[8*i+j] as u64) << (8*j)`, i.e. byte `src[base + j]`
contributes bits `[8j, 8j+8)`.

`Array.getD … 0` keeps the oracle total without bounds arguments; every
theorem applies it under `src.val.size = dst.val.size * 8`, so for an
in-range output index the accessed bytes are exactly the real slice
bytes. -/
private def leDecode (src : RustSlice u8) (base : Nat) : Nat :=
  (src.val.getD base (0 : u8)).toNat
    + (src.val.getD (base + 1) (0 : u8)).toNat * 2 ^ 8
    + (src.val.getD (base + 2) (0 : u8)).toNat * 2 ^ 16
    + (src.val.getD (base + 3) (0 : u8)).toNat * 2 ^ 24
    + (src.val.getD (base + 4) (0 : u8)).toNat * 2 ^ 32
    + (src.val.getD (base + 5) (0 : u8)).toNat * 2 ^ 40
    + (src.val.getD (base + 6) (0 : u8)).toNat * 2 ^ 48
    + (src.val.getD (base + 7) (0 : u8)).toNat * 2 ^ 56

/-! ## Generic scaffolding (pattern reused from `big_endian_read_u64_into`,
`big_endian_from_slice_u64`, `clever_009_rolling_max`). -/

/-- `RustM.ok x >>= f = f x`. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem uzero : (0 : usize).toNat = 0 := by decide
private theorem usize_one_toNat : (1 : usize).toNat = 1 := by decide
private theorem ulit2 : (2 : usize).toNat = 2 := by decide
private theorem ulit3 : (3 : usize).toNat = 3 := by decide
private theorem ulit4 : (4 : usize).toNat = 4 := by decide
private theorem ulit5 : (5 : usize).toNat = 5 := by decide
private theorem ulit6 : (6 : usize).toNat = 6 := by decide
private theorem ulit7 : (7 : usize).toNat = 7 := by decide
private theorem ulit8 : (8 : usize).toNat = 8 := by decide
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- Push a single element (1-chunk `extend_from_slice`). -/
private def push_one (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Primitive-operator reduction lemmas for `read_le_u64`. -/

/-- Indexing a slice in-bounds. -/
private theorem idx_ok (src : RustSlice u8) (v : usize)
    (h : v.toNat < src.val.size) :
    (src[v]_? : RustM u8) = RustM.ok (src.val[v.toNat]'h) := by
  show (if h : v.toNat < src.val.size then pure (src.val[v])
          else .fail .arrayOutOfBounds) = RustM.ok (src.val[v.toNat]'h)
  rw [dif_pos h]; rfl

/-- `usize` addition without overflow. -/
private theorem add_ok (base k : usize) (h : base.toNat + k.toNat < 2^64) :
    (base +? k : RustM usize) = RustM.ok (base + k) := by
  show (rust_primitives.ops.arith.Add.add base k : RustM usize) = RustM.ok (base + k)
  show (if BitVec.uaddOverflow base.toBitVec k.toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (base + k)) = _
  have hbv : BitVec.uaddOverflow base.toBitVec k.toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow base.toBitVec k.toBitVec = bo
    cases bo with
    | false => rfl
    | true => exact absurd ((USize64.uaddOverflow_iff base k).mp hbo) (by omega)
  rw [hbv]; rfl

/-- `usize` multiplication without overflow. -/
private theorem mul_ok (base k : usize) (h : base.toNat * k.toNat < 2^64) :
    (base *? k : RustM usize) = RustM.ok (base * k) := by
  show (rust_primitives.ops.arith.Mul.mul base k : RustM usize) = RustM.ok (base * k)
  show (if BitVec.umulOverflow base.toBitVec k.toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (base * k)) = _
  have hbv : BitVec.umulOverflow base.toBitVec k.toBitVec = false := by
    generalize hbo : BitVec.umulOverflow base.toBitVec k.toBitVec = bo
    cases bo with
    | false => rfl
    | true => exact absurd ((USize64.umulOverflow_iff base k).mp hbo) (by omega)
  rw [hbv]; rfl

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

/-! ## Byte-assembly form of `read_le_u64`.

Little-endian: the byte at the lowest index (`b0 = src[base]`) is the
*least* significant (no shift); `b7 = src[base+7]` is the most
significant (shift 56). -/

/-- The OR-of-cast-and-shift form produced by reducing `read_le_u64`'s
    body.  `|||` is left-associative and binds looser than `<<<`, so this
    is exactly the left-nested OR the extracted code builds. -/
private def leExpr (b0 b1 b2 b3 b4 b5 b6 b7 : u8) : u64 :=
  UInt8.toUInt64 b0
    ||| UInt8.toUInt64 b1 <<< (8 : UInt64)
    ||| UInt8.toUInt64 b2 <<< (16 : UInt64)
    ||| UInt8.toUInt64 b3 <<< (24 : UInt64)
    ||| UInt8.toUInt64 b4 <<< (32 : UInt64)
    ||| UInt8.toUInt64 b5 <<< (40 : UInt64)
    ||| UInt8.toUInt64 b6 <<< (48 : UInt64)
    ||| UInt8.toUInt64 b7 <<< (56 : UInt64)

/-- `Array.getD` on an in-bounds index is `getElem`. -/
private theorem arr_getD (a : Array u8) (i : Nat) (h : i < a.size) :
    a.getD i (0 : u8) = a[i]'h := by
  simp [Array.getD, h]

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
      = b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16
        + b3.toNat * 2 ^ 24 + b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40
        + b6.toNat * 2 ^ 48 + b7.toNat * 2 ^ 56 := by
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
      = b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16
        + b3.toNat * 2 ^ 24 + b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40
        + b6.toNat * 2 ^ 48 + b7.toNat * 2 ^ 56 := by
  have h := congrArg BitVec.toNat (leExpr_toBitVec b0 b1 b2 b3 b4 b5 b6 b7)
  rw [leBV_toNat] at h
  simpa using h

/-! ## `read_le_u64` reduction.

`read_le_u64 src base` does eight in-bounds partial slice reads
`src[base + k]_?`, eight widening casts, seven shifts and seven ORs. With
`base + 8 ≤ src.len()` all reads succeed and the address arithmetic never
overflows, so the body reduces to `RustM.ok (leExpr …)` whose `.toNat` is
the little-endian oracle `leDecode`. -/
private theorem read_le_u64_spec (src : RustSlice u8) (base : usize)
    (hb : base.toNat + 8 ≤ src.val.size) :
    ∃ r : u64,
      little_endian_read_u64_into.read_le_u64 src base = RustM.ok r ∧
      r.toNat = leDecode src base.toNat := by
  have hsz : src.val.size < USize64.size := src.size_lt_usizeSize
  have hszN : src.val.size < 2 ^ 64 := by rw [← usize_size_eq]; exact hsz
  have hb0 : base.toNat < src.val.size := by omega
  have ha1 : (base +? (1 : usize) : RustM usize) = RustM.ok (base + 1) :=
    add_ok base 1 (by rw [usize_one_toNat]; omega)
  have ha2 : (base +? (2 : usize) : RustM usize) = RustM.ok (base + 2) :=
    add_ok base 2 (by rw [ulit2]; omega)
  have ha3 : (base +? (3 : usize) : RustM usize) = RustM.ok (base + 3) :=
    add_ok base 3 (by rw [ulit3]; omega)
  have ha4 : (base +? (4 : usize) : RustM usize) = RustM.ok (base + 4) :=
    add_ok base 4 (by rw [ulit4]; omega)
  have ha5 : (base +? (5 : usize) : RustM usize) = RustM.ok (base + 5) :=
    add_ok base 5 (by rw [ulit5]; omega)
  have ha6 : (base +? (6 : usize) : RustM usize) = RustM.ok (base + 6) :=
    add_ok base 6 (by rw [ulit6]; omega)
  have ha7 : (base +? (7 : usize) : RustM usize) = RustM.ok (base + 7) :=
    add_ok base 7 (by rw [ulit7]; omega)
  have hb1n : (base + 1).toNat = base.toNat + 1 := by
    rw [USize64.toNat_add_of_lt (by rw [usize_one_toNat]; omega), usize_one_toNat]
  have hb2n : (base + 2).toNat = base.toNat + 2 := by
    rw [USize64.toNat_add_of_lt (by rw [ulit2]; omega), ulit2]
  have hb3n : (base + 3).toNat = base.toNat + 3 := by
    rw [USize64.toNat_add_of_lt (by rw [ulit3]; omega), ulit3]
  have hb4n : (base + 4).toNat = base.toNat + 4 := by
    rw [USize64.toNat_add_of_lt (by rw [ulit4]; omega), ulit4]
  have hb5n : (base + 5).toNat = base.toNat + 5 := by
    rw [USize64.toNat_add_of_lt (by rw [ulit5]; omega), ulit5]
  have hb6n : (base + 6).toNat = base.toNat + 6 := by
    rw [USize64.toNat_add_of_lt (by rw [ulit6]; omega), ulit6]
  have hb7n : (base + 7).toNat = base.toNat + 7 := by
    rw [USize64.toNat_add_of_lt (by rw [ulit7]; omega), ulit7]
  have hi0 : base.toNat < src.val.size := by omega
  have hi1 : base.toNat + 1 < src.val.size := by omega
  have hi2 : base.toNat + 2 < src.val.size := by omega
  have hi3 : base.toNat + 3 < src.val.size := by omega
  have hi4 : base.toNat + 4 < src.val.size := by omega
  have hi5 : base.toNat + 5 < src.val.size := by omega
  have hi6 : base.toNat + 6 < src.val.size := by omega
  have hi7 : base.toNat + 7 < src.val.size := by omega
  have hI0 := idx_ok src base hb0
  have hI1 := idx_ok src (base + 1) (by rw [hb1n]; omega)
  have hI2 := idx_ok src (base + 2) (by rw [hb2n]; omega)
  have hI3 := idx_ok src (base + 3) (by rw [hb3n]; omega)
  have hI4 := idx_ok src (base + 4) (by rw [hb4n]; omega)
  have hI5 := idx_ok src (base + 5) (by rw [hb5n]; omega)
  have hI6 := idx_ok src (base + 6) (by rw [hb6n]; omega)
  have hI7 := idx_ok src (base + 7) (by rw [hb7n]; omega)
  have hs56 : (0 ≤ (56 : i32) && (56 : i32) < 64) = true := by decide
  have hs48 : (0 ≤ (48 : i32) && (48 : i32) < 64) = true := by decide
  have hs40 : (0 ≤ (40 : i32) && (40 : i32) < 64) = true := by decide
  have hs32 : (0 ≤ (32 : i32) && (32 : i32) < 64) = true := by decide
  have hs24 : (0 ≤ (24 : i32) && (24 : i32) < 64) = true := by decide
  have hs16 : (0 ≤ (16 : i32) && (16 : i32) < 64) = true := by decide
  have hs8  : (0 ≤ (8 : i32) && (8 : i32) < 64) = true := by decide
  have e56 : ((56 : i32).toNatClampNeg).toUInt64 = (56 : UInt64) := by decide
  have e48 : ((48 : i32).toNatClampNeg).toUInt64 = (48 : UInt64) := by decide
  have e40 : ((40 : i32).toNatClampNeg).toUInt64 = (40 : UInt64) := by decide
  have e32 : ((32 : i32).toNatClampNeg).toUInt64 = (32 : UInt64) := by decide
  have e24 : ((24 : i32).toNatClampNeg).toUInt64 = (24 : UInt64) := by decide
  have e16 : ((16 : i32).toNatClampNeg).toUInt64 = (16 : UInt64) := by decide
  have e8  : ((8 : i32).toNatClampNeg).toUInt64 = (8 : UInt64) := by decide
  refine ⟨leExpr (src.val[base.toNat]'hi0)
            (src.val[base.toNat + 1]'hi1) (src.val[base.toNat + 2]'hi2)
            (src.val[base.toNat + 3]'hi3) (src.val[base.toNat + 4]'hi4)
            (src.val[base.toNat + 5]'hi5) (src.val[base.toNat + 6]'hi6)
            (src.val[base.toNat + 7]'hi7), ?_, ?_⟩
  · simp only [little_endian_read_u64_into.read_le_u64,
               hI0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
               hb1n, hb2n, hb3n, hb4n, hb5n, hb6n, hb7n,
               hI1, hI2, hI3, hI4, hI5, hI6, hI7, cast_ok,
               shl_ok _ (56 : i32) hs56, shl_ok _ (48 : i32) hs48,
               shl_ok _ (40 : i32) hs40, shl_ok _ (32 : i32) hs32,
               shl_ok _ (24 : i32) hs24, shl_ok _ (16 : i32) hs16,
               shl_ok _ (8 : i32) hs8, e56, e48, e40, e32, e24, e16, e8,
               or_ok, leExpr, RustM_ok_bind]
  · rw [leExpr_toNat]
    unfold leDecode
    simp only [arr_getD src.val base.toNat hi0,
        arr_getD src.val (base.toNat + 1) hi1,
        arr_getD src.val (base.toNat + 2) hi2,
        arr_getD src.val (base.toNat + 3) hi3,
        arr_getD src.val (base.toNat + 4) hi4,
        arr_getD src.val (base.toNat + 5) hi5,
        arr_getD src.val (base.toNat + 6) hi6,
        arr_getD src.val (base.toNat + 7) hi7]

/-! ## `build_values` step lemmas. -/

private theorem build_values_oob
    (src : RustSlice u8) (i count : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : count.toNat ≤ i.toNat) :
    little_endian_read_u64_into.build_values src i count acc = RustM.ok acc := by
  conv => lhs; unfold little_endian_read_u64_into.build_values
  have h_cond : decide (i ≥ count) = true := by
    rw [decide_eq_true_iff]
    show count ≤ i
    rw [USize64.le_iff_toNat_le]
    exact hi
  simp only [rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

private theorem build_values_step
    (src : RustSlice u8) (i count : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < count.toNat)
    (h_acc : acc.val.size + 1 < USize64.size)
    (hmul : i.toNat * 8 < 2 ^ 64)
    (r : u64)
    (hr : little_endian_read_u64_into.read_le_u64 src (i * 8) = RustM.ok r) :
    little_endian_read_u64_into.build_values src i count acc =
      little_endian_read_u64_into.build_values src (i + 1) count
        (push_one acc r h_acc) := by
  conv => lhs; unfold little_endian_read_u64_into.build_values
  have h_cond : decide (i ≥ count) = false := by
    rw [decide_eq_false_iff_not]
    show ¬ count ≤ i
    rw [USize64.le_iff_toNat_le]
    omega
  have h_mul : (i *? (8 : usize) : RustM usize) = RustM.ok (i * 8) := by
    apply mul_ok; rw [ulit8]; exact hmul
  have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by omega
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    add_ok i 1 (by rw [usize_one_toNat]; omega)
  simp only [rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte, h_mul, hr]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[r] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
            = RustM.ok ⟨#[r], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[r] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
              ⟨#[r], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (push_one acc r h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_eq]
  rfl

/-! ## Strong induction for `build_values`.

Invariant: `acc.val.size = i.toNat`, and `acc` holds the little-endian
decode of every chunk seen so far. The precondition
`src.val.size = count.toNat * 8` makes every chunk read in-bounds. -/

private theorem build_values_correct (src : RustSlice u8) (count : usize)
    (hsrc : src.val.size = count.toNat * 8) :
    ∀ (k : Nat) (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global),
      count.toNat - i.toNat ≤ k →
      i.toNat ≤ count.toNat →
      acc.val.size = i.toNat →
      (∀ (j : Nat) (hj : j < acc.val.size),
          (acc.val[j]'hj).toNat = leDecode src (j * 8)) →
      ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
        little_endian_read_u64_into.build_values src i count acc = RustM.ok v ∧
        v.val.size = count.toNat ∧
        (∀ (j : Nat) (hj : j < v.val.size),
            (v.val[j]'hj).toNat = leDecode src (j * 8)) := by
  have hcszN : count.toNat * 8 < 2 ^ 64 := by
    have h := src.size_lt_usizeSize
    rw [hsrc, usize_size_eq] at h
    exact h
  have hcsz : count.toNat < USize64.size := by
    rw [usize_size_eq]; omega
  intro k
  induction k with
  | zero =>
    intro i acc hk hi_le h_acc_size h_acc_chunk
    have hi_eq : i.toNat = count.toNat := by omega
    have hi_ge : count.toNat ≤ i.toNat := by omega
    refine ⟨acc, build_values_oob src i count acc hi_ge, ?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intro j hj; exact h_acc_chunk j hj
  | succ k ih =>
    intro i acc hk hi_le h_acc_size h_acc_chunk
    by_cases hi_ge : count.toNat ≤ i.toNat
    · have hi_eq : i.toNat = count.toNat := by omega
      refine ⟨acc, build_values_oob src i count acc hi_ge, ?_, ?_⟩
      · rw [h_acc_size, hi_eq]
      · intro j hj; exact h_acc_chunk j hj
    · have hi_lt : i.toNat < count.toNat := Nat.lt_of_not_le hi_ge
      have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, usize_size_eq]; omega
      have hmul : i.toNat * 8 < 2 ^ 64 := by omega
      have h_mul_toNat : (i * 8).toNat = i.toNat * 8 := by
        rw [USize64.toNat_mul_of_lt (by rw [ulit8]; exact hmul), ulit8]
      have h_chunk_bound : (i * 8).toNat + 8 ≤ src.val.size := by
        rw [h_mul_toNat, hsrc]; omega
      obtain ⟨r, hr, hr_val⟩ := read_le_u64_spec src (i * 8) h_chunk_bound
      have h_step := build_values_step src i count acc hi_lt h_acc_succ hmul r hr
      rw [h_step]
      have h_acc'_size :
          (push_one acc r h_acc_succ).val.size = (i + 1).toNat := by
        show (acc.val ++ #[r]).size = (i + 1).toNat
        rw [Array.size_append, h_i1, h_acc_size]; rfl
      have h_acc'_chunk :
          ∀ (j : Nat) (hj : j < (push_one acc r h_acc_succ).val.size),
            ((push_one acc r h_acc_succ).val[j]'hj).toNat = leDecode src (j * 8) := by
        intro j hj
        show ((acc.val ++ #[r])[j]'hj).toNat = _
        by_cases hjlt : j < acc.val.size
        · rw [Array.getElem_append_left hjlt]
          exact h_acc_chunk j hjlt
        · have h_size_raw : (acc.val ++ #[r]).size = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          have hj_eq : j = acc.val.size := by
            have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
            omega
          subst hj_eq
          rw [Array.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self]
          show r.toNat = leDecode src (acc.val.size * 8)
          rw [hr_val, h_mul_toNat, h_acc_size]
      have h_i1_le : (i + 1).toNat ≤ count.toNat := by rw [h_i1]; omega
      have h_k_le : count.toNat - (i + 1).toNat ≤ k := by rw [h_i1]; omega
      exact ih (i + 1) _ h_k_le h_i1_le h_acc'_size h_acc'_chunk

/-! ## Top-level reduction.

`read_u64_into` asserts `src.len() = dst.len()*8`, then builds the decoded
buffer from the empty `Vec` and writes it back with `copy_from_slice`
(which returns its `src` argument). -/

private theorem read_u64_into_eq_build (src : RustSlice u8) (dst : RustSlice u64)
    (hpre : src.val.size = dst.val.size * 8) :
    little_endian_read_u64_into.read_u64_into src dst
      = little_endian_read_u64_into.build_values src (0 : usize)
          (USize64.ofNat dst.val.size) ⟨(List.nil).toArray, by grind⟩ := by
  have hsz : src.val.size < USize64.size := src.size_lt_usizeSize
  have hszN : src.val.size < 2 ^ 64 := by rw [← usize_size_eq]; exact hsz
  have hdszN : dst.val.size * 8 < 2 ^ 64 := by rw [← hpre]; exact hszN
  have hdsz : dst.val.size < USize64.size := by rw [usize_size_eq]; omega
  have h_len_src :
      (core_models.slice.Impl.len u8 src : RustM usize)
        = RustM.ok (USize64.ofNat src.val.size) := rfl
  have h_len_dst :
      (core_models.slice.Impl.len u64 dst : RustM usize)
        = RustM.ok (USize64.ofNat dst.val.size) := rfl
  have h_mul :
      ((USize64.ofNat dst.val.size) *? (8 : usize) : RustM usize)
        = RustM.ok (USize64.ofNat dst.val.size * 8) := by
    apply mul_ok
    rw [USize64.toNat_ofNat_of_lt' hdsz, ulit8]; exact hdszN
  have h_eq_bool :
      ((USize64.ofNat src.val.size) == (USize64.ofNat dst.val.size * 8)) = true := by
    rw [beq_iff_eq]
    apply USize64.toNat_inj.mp
    rw [USize64.toNat_ofNat_of_lt' hsz,
        USize64.toNat_mul_of_lt (by rw [USize64.toNat_ofNat_of_lt' hdsz, ulit8]; exact hdszN),
        USize64.toNat_ofNat_of_lt' hdsz, ulit8]
    exact hpre
  have h_new :
      (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  unfold little_endian_read_u64_into.read_u64_into
  simp only [h_len_src, h_len_dst, RustM_ok_bind, h_mul,
             rust_primitives.cmp.eq, h_eq_bool, hax_lib.assert, ↓reduceIte,
             pure_bind, h_new, core_models.ops.deref.Deref.deref,
             core_models.slice.Impl.copy_from_slice, rust_primitives.mem.replace,
             bind_pure]

private theorem read_u64_into_aux (src : RustSlice u8) (dst : RustSlice u64)
    (hpre : src.val.size = dst.val.size * 8) :
    ∃ v : RustSlice u64,
      little_endian_read_u64_into.read_u64_into src dst = RustM.ok v ∧
      v.val.size = dst.val.size ∧
      (∀ (j : Nat) (hj : j < v.val.size),
          (v.val[j]'hj).toNat = leDecode src (j * 8)) := by
  have hsz : src.val.size < USize64.size := src.size_lt_usizeSize
  have hszN : src.val.size < 2 ^ 64 := by rw [← usize_size_eq]; exact hsz
  have hdsz : dst.val.size < USize64.size := by rw [usize_size_eq]; omega
  have hdsz' : (USize64.ofNat dst.val.size).toNat = dst.val.size :=
    USize64.toNat_ofNat_of_lt' hdsz
  have hsrc' : src.val.size = (USize64.ofNat dst.val.size).toNat * 8 := by
    rw [hdsz']; exact hpre
  have h_acc0_chunk :
      ∀ (j : Nat)
        (hj : j < (⟨(List.nil).toArray, by grind⟩
                    : alloc.vec.Vec u64 alloc.alloc.Global).val.size),
        (((⟨(List.nil).toArray, by grind⟩
            : alloc.vec.Vec u64 alloc.alloc.Global).val[j]'hj).toNat)
          = leDecode src (j * 8) := by
    intro j hj; exact absurd hj (by simp)
  obtain ⟨v, hv, hv_size, hv_chunk⟩ :=
    build_values_correct src (USize64.ofNat dst.val.size) hsrc'
      (USize64.ofNat dst.val.size).toNat (0 : usize)
      ⟨(List.nil).toArray, by grind⟩ (by rw [uzero]; omega) (by rw [uzero]; omega)
      (by rw [uzero]; rfl) h_acc0_chunk
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [read_u64_into_eq_build src dst hpre]; exact hv
  · rw [hv_size, hdsz']
  · intro j hj; exact hv_chunk j hj

private theorem read_u64_into_fail_aux (src : RustSlice u8) (dst : RustSlice u64)
    (hno : dst.val.size * 8 < USize64.size)
    (hmis : src.val.size ≠ dst.val.size * 8) :
    little_endian_read_u64_into.read_u64_into src dst
      = RustM.fail Error.assertionFailure := by
  have hsz : src.val.size < USize64.size := src.size_lt_usizeSize
  have hszN : src.val.size < 2 ^ 64 := by rw [← usize_size_eq]; exact hsz
  have hnoN : dst.val.size * 8 < 2 ^ 64 := by rw [← usize_size_eq]; exact hno
  have hdsz : dst.val.size < USize64.size := by rw [usize_size_eq]; omega
  have h_len_src :
      (core_models.slice.Impl.len u8 src : RustM usize)
        = RustM.ok (USize64.ofNat src.val.size) := rfl
  have h_len_dst :
      (core_models.slice.Impl.len u64 dst : RustM usize)
        = RustM.ok (USize64.ofNat dst.val.size) := rfl
  have h_mul :
      ((USize64.ofNat dst.val.size) *? (8 : usize) : RustM usize)
        = RustM.ok (USize64.ofNat dst.val.size * 8) := by
    apply mul_ok
    rw [USize64.toNat_ofNat_of_lt' hdsz, ulit8]; exact hnoN
  have h_eq_bool :
      ((USize64.ofNat src.val.size) == (USize64.ofNat dst.val.size * 8)) = false := by
    rw [← Bool.not_eq_true, beq_iff_eq]
    intro hC
    apply hmis
    have := congrArg USize64.toNat hC
    rw [USize64.toNat_ofNat_of_lt' hsz,
        USize64.toNat_mul_of_lt (by rw [USize64.toNat_ofNat_of_lt' hdsz, ulit8]; exact hnoN),
        USize64.toNat_ofNat_of_lt' hdsz, ulit8] at this
    exact this
  unfold little_endian_read_u64_into.read_u64_into
  simp only [h_len_src, h_len_dst, RustM_ok_bind, h_mul,
             rust_primitives.cmp.eq, h_eq_bool, hax_lib.assert,
             Bool.false_eq_true, ↓reduceIte, pure_bind]
  rfl

/-! ## Obligations.

Proofs discharged via the ported scaffolding above; the contract surface
is identical to the closed-proof `big_endian_read_u64_into` reference up
to the oracle's byte weighting (little-endian: `src[base]` is least
significant). -/

/-- Failure condition. Captures the `#[should_panic]` tests
    `slice_len_too_small_u64_read_little_endian` (15 bytes vs 2 longs) and
    `slice_len_too_big_u64_read_little_endian` (17 bytes vs 2 longs), and
    the property test `prop_length_mismatch_panics`: whenever the exact
    relation `src.len() == dst.len() * 8` does **not** hold, the modeled
    `hax_lib::assert!` fires and the function fails with an assertion
    failure (the original `assert_eq!` panic). The `hno` hypothesis pins
    the failure mode to the assertion path (the regime the tests
    exercise); without it an over-long `dst` would instead trip the
    `usize` overflow of `dst.len() * 8`. The general `≠` form covers
    mismatches in both directions, as the property test does. -/
theorem read_u64_into_length_mismatch_fails
    (src : RustSlice u8) (dst : RustSlice u64)
    (hno : dst.val.size * 8 < USize64.size)
    (hmis : src.val.size ≠ dst.val.size * 8) :
    little_endian_read_u64_into.read_u64_into src dst
      = RustM.fail Error.assertionFailure :=
  read_u64_into_fail_aux src dst hno hmis

/-- Totality / no-panic on valid input. Captures the "completes without
    panicking" assertion implicit in
    `prop_little_endian_decode_postcondition` and in the
    `doc_example_little_endian_roundtrip` doc-test: when the precondition
    `src.len() == dst.len() * 8` holds, the function returns successfully
    (the assert passes, `build_values`' decreasing recursion terminates,
    and every `extend_from_slice` stays within `usize` because the final
    buffer length equals `dst.len()`). -/
theorem read_u64_into_valid_succeeds
    (src : RustSlice u8) (dst : RustSlice u64)
    (hpre : src.val.size = dst.val.size * 8) :
    ∃ v : RustSlice u64,
      little_endian_read_u64_into.read_u64_into src dst = RustM.ok v := by
  obtain ⟨v, hv, _, _⟩ := read_u64_into_aux src dst hpre
  exact ⟨v, hv⟩

/-- Length-preservation postcondition. Captures the per-chunk-one-element
    structure exercised by `prop_little_endian_decode_postcondition`
    (`dst` has exactly `count` elements, each compared) and the
    `numbers_got: [u64; 4]` shape of `doc_example_little_endian_roundtrip`:
    the rewritten slice holds exactly `dst.len()` elements (`build_values`
    emits exactly one element per chunk, and `copy_from_slice` preserves
    `dst`'s length). -/
theorem read_u64_into_preserves_length
    (src : RustSlice u8) (dst : RustSlice u64)
    (hpre : src.val.size = dst.val.size * 8)
    (v : RustSlice u64)
    (hres : little_endian_read_u64_into.read_u64_into src dst = RustM.ok v) :
    v.val.size = dst.val.size := by
  obtain ⟨v', hv', hsz, _⟩ := read_u64_into_aux src dst hpre
  rw [hv'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hsz

/-- Core functional postcondition. Captures
    `prop_little_endian_decode_postcondition` (and the
    `doc_example_little_endian_roundtrip` doc-test, a concrete instance):
    each output element `v[i]` is the **little-endian** decode of the
    8-byte chunk `src[8*i .. 8*i+8]`, taken at its own index. The oracle
    `leDecode` weights the lowest source index (`src[8*i]`) by `2^0`
    (least significant), so this falsifies any implementation that uses
    the wrong endianness, maps a chunk to the wrong element, reverses
    element order, or drops/skips chunks. -/
theorem read_u64_into_elementwise_le
    (src : RustSlice u8) (dst : RustSlice u64)
    (hpre : src.val.size = dst.val.size * 8)
    (v : RustSlice u64)
    (hres : little_endian_read_u64_into.read_u64_into src dst = RustM.ok v)
    (i : Nat) (hi : i < v.val.size) :
    (v.val[i]'hi).toNat = leDecode src (i * 8) := by
  obtain ⟨v', hv', _, hchunk⟩ := read_u64_into_aux src dst hpre
  rw [hv'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hchunk i hi

/-- Empty-slice edge case. Captures the `count == 0` iteration of
    `prop_little_endian_decode_postcondition` (the valid empty-slice
    case): on empty `src`/`dst` the precondition `0 == 0 * 8` holds, so
    the call is a valid no-op — the function completes successfully and
    yields an empty slice (`build_values`' base case fires immediately and
    the whole-slice `copy_from_slice` write-back is a no-op). -/
theorem read_u64_into_empty_noop
    (src : RustSlice u8) (dst : RustSlice u64)
    (hsrc : src.val.size = 0) (hdst : dst.val.size = 0) :
    ∃ v : RustSlice u64,
      little_endian_read_u64_into.read_u64_into src dst = RustM.ok v ∧
      v.val.size = 0 := by
  have hpre : src.val.size = dst.val.size * 8 := by rw [hsrc, hdst]
  obtain ⟨v, hv, hsz, _⟩ := read_u64_into_aux src dst hpre
  exact ⟨v, hv, by rw [hsz, hdst]⟩

end Little_endian_read_u64_intoObligations
