
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace big_endian_write_u64

--  Build the target image of `buf`: bytes `0..8` are `be`, bytes `8..`
--  are copied unchanged from `buf`, appended to `acc`.
@[spec]
def build_output
    (buf : (RustSlice u8))
    (be : (RustArray u8 8))
    (i : usize)
    (acc : (alloc.vec.Vec u8 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len u8 buf)))) then do
    (pure acc)
  else do
    let acc : (alloc.vec.Vec u8 alloc.alloc.Global) := acc;
    let byte : u8 ← if (← (i <? (8 : usize))) then do be[i]_? else do buf[i]_?;
    let chunk : (RustArray u8 1) := (RustArray.ofVec #v[byte]);
    let acc : (alloc.vec.Vec u8 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (build_output buf be (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def write_u64 (buf : (RustSlice u8)) (n : u64) : RustM (RustSlice u8) := do
  let _ ←
    (hax_lib.assert
      (← ((← (core_models.slice.Impl.len u8 buf)) >=? (8 : usize))));
  let be : (RustArray u8 8) :=
    (RustArray.ofVec #v[(← (rust_primitives.hax.cast_op
                            (← (n >>>? (56 : i32))) :
                            RustM u8)),
                          (← (rust_primitives.hax.cast_op
                            (← (n >>>? (48 : i32))) :
                            RustM u8)),
                          (← (rust_primitives.hax.cast_op
                            (← (n >>>? (40 : i32))) :
                            RustM u8)),
                          (← (rust_primitives.hax.cast_op
                            (← (n >>>? (32 : i32))) :
                            RustM u8)),
                          (← (rust_primitives.hax.cast_op
                            (← (n >>>? (24 : i32))) :
                            RustM u8)),
                          (← (rust_primitives.hax.cast_op
                            (← (n >>>? (16 : i32))) :
                            RustM u8)),
                          (← (rust_primitives.hax.cast_op
                            (← (n >>>? (8 : i32))) :
                            RustM u8)),
                          (← (rust_primitives.hax.cast_op n : RustM u8))]);
  let out : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (build_output
      buf
      be
      (0 : usize)
      (← (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk)));
  let buf : (RustSlice u8) ←
    (core_models.slice.Impl.copy_from_slice u8
      buf
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) out)));
  (pure buf)

end big_endian_write_u64

