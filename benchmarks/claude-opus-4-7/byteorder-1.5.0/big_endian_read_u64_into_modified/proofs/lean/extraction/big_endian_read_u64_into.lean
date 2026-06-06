
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


namespace big_endian_read_u64_into

--  Big-endian decode of the 8 bytes at `src[base .. base + 8]`.
@[spec]
def read_be_u64 (src : (RustSlice u8)) (base : usize) : RustM u64 := do
  ((← ((← ((← ((← ((← ((← ((← ((← (rust_primitives.hax.cast_op
                    (← src[base]_?) :
                    RustM u64))
                  <<<? (56 : i32)))
                |||? (← ((← (rust_primitives.hax.cast_op
                    (← src[(← (base +? (1 : usize)))]_?) :
                    RustM u64))
                  <<<? (48 : i32)))))
              |||? (← ((← (rust_primitives.hax.cast_op
                  (← src[(← (base +? (2 : usize)))]_?) :
                  RustM u64))
                <<<? (40 : i32)))))
            |||? (← ((← (rust_primitives.hax.cast_op
                (← src[(← (base +? (3 : usize)))]_?) :
                RustM u64))
              <<<? (32 : i32)))))
          |||? (← ((← (rust_primitives.hax.cast_op
              (← src[(← (base +? (4 : usize)))]_?) :
              RustM u64))
            <<<? (24 : i32)))))
        |||? (← ((← (rust_primitives.hax.cast_op
            (← src[(← (base +? (5 : usize)))]_?) :
            RustM u64))
          <<<? (16 : i32)))))
      |||? (← ((← (rust_primitives.hax.cast_op
          (← src[(← (base +? (6 : usize)))]_?) :
          RustM u64))
        <<<? (8 : i32)))))
    |||? (← (rust_primitives.hax.cast_op
      (← src[(← (base +? (7 : usize)))]_?) :
      RustM u64)))

--  Build the decoded image of `dst`: element `i` is the big-endian
--  decode of `src[8*i .. 8*i + 8]`, for `i` in `0 .. count`, appended to
--  `acc`.
@[spec]
def build_values
    (src : (RustSlice u8))
    (i : usize)
    (count : usize)
    (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (i >=? count)) then do
    (pure acc)
  else do
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
    let chunk : (RustArray u64 1) :=
      (RustArray.ofVec #v[(← (read_be_u64 src (← (i *? (8 : usize)))))]);
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (build_values src (← (i +? (1 : usize))) count acc)
partial_fixpoint

@[spec]
def read_u64_into (src : (RustSlice u8)) (dst : (RustSlice u64)) :
    RustM (RustSlice u64) := do
  let _ ←
    (hax_lib.assert
      (← ((← (core_models.slice.Impl.len u8 src))
        ==? (← ((← (core_models.slice.Impl.len u64 dst)) *? (8 : usize))))));
  let count : usize ← (core_models.slice.Impl.len u64 dst);
  let values : (alloc.vec.Vec u64 alloc.alloc.Global) ←
    (build_values
      src
      (0 : usize)
      count
      (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)));
  let dst : (RustSlice u64) ←
    (core_models.slice.Impl.copy_from_slice u64
      dst
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u64 alloc.alloc.Global) values)));
  (pure dst)

end big_endian_read_u64_into

