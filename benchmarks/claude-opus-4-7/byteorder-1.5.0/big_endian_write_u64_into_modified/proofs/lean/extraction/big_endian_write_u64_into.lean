
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


namespace big_endian_write_u64_into

--  Build the output image of `dst`: bytes `8*i .. 8*i + 8` are the
--  big-endian encoding of `src[i]`, for `i` in `0 .. src.len()`,
--  appended to `acc`.
@[spec]
def build_output
    (src : (RustSlice u64))
    (i : usize)
    (acc : (alloc.vec.Vec u8 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 src)))) then do
    (pure acc)
  else do
    let n : u64 ← src[i]_?;
    let acc : (alloc.vec.Vec u8 alloc.alloc.Global) := acc;
    let chunk : (RustArray u8 8) :=
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
    let acc : (alloc.vec.Vec u8 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (build_output src (← (i +? (1 : usize))) acc)
partial_fixpoint

--  Writes unsigned 64 bit integers from `src` into `dst` in big-endian order.
-- 
--  # Panics
-- 
--  Panics when `dst.len() != 8 * src.len()`.
@[spec]
def write_u64_into (src : (RustSlice u64)) (dst : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let _ ←
    (hax_lib.assert
      (← ((← ((← (core_models.slice.Impl.len u64 src)) *? (8 : usize)))
        ==? (← (core_models.slice.Impl.len u8 dst)))));
  let out : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (build_output
      src
      (0 : usize)
      (← (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk)));
  let dst : (RustSlice u8) ←
    (core_models.slice.Impl.copy_from_slice u8
      dst
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) out)));
  (pure dst)

end big_endian_write_u64_into

