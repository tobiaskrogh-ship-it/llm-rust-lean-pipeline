
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


namespace little_endian_from_slice_u64

--  Byte-swap a `u64` (little-endian conversion on a big-endian host).
-- 
--  Inlined replacement for `u64::to_le`: the method extracts to
--  `core_models.num.Impl_*.to_le`, which the Hax Lean prelude does not
--  define (`lake build` would fail with an `Unknown identifier`). The
--  shift/mask form uses only `&`, `<<`, `>>`, `|` over `u64`, all of
--  which Hax models. Inside the `cfg!(target_endian = "big")` branch the
--  host is big-endian, where `u64::to_le()` is exactly
--  `u64::swap_bytes()`, so this substitution is semantics-preserving.
@[spec]
def swap_bytes_u64 (x : u64) : RustM u64 := do
  ((← ((← ((← ((← ((← ((← ((← ((← (x &&&? (255 : u64))) <<<? (56 : i32)))
                |||? (← ((← (x &&&? (65280 : u64))) <<<? (40 : i32)))))
              |||? (← ((← (x &&&? (16711680 : u64))) <<<? (24 : i32)))))
            |||? (← ((← (x &&&? (4278190080 : u64))) <<<? (8 : i32)))))
          |||? (← ((← (x &&&? (1095216660480 : u64))) >>>? (8 : i32)))))
        |||? (← ((← (x &&&? (280375465082880 : u64))) >>>? (24 : i32)))))
      |||? (← ((← (x &&&? (71776119061217280 : u64))) >>>? (40 : i32)))))
    |||? (← ((← (x &&&? (18374686479671623680 : u64))) >>>? (56 : i32))))

--  Build the byte-swapped image of `numbers[i..]`, appended to `acc`.
@[spec]
def build_swapped
    (numbers : (RustSlice u64))
    (i : usize)
    (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 numbers)))) then do
    (pure acc)
  else do
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
    let chunk : (RustArray u64 1) :=
      (RustArray.ofVec #v[(← (swap_bytes_u64 (← numbers[i]_?)))]);
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (build_swapped numbers (← (i +? (1 : usize))) acc)
partial_fixpoint

--  Converts the given slice of unsigned 64 bit integers to little endian.
-- 
--  If the host platform is already little endian, this is a no-op.
@[spec]
def from_slice_u64 (numbers : (RustSlice u64)) : RustM (RustSlice u64) := do
  let numbers : (RustSlice u64) ←
    if false then do
      let swapped : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        (build_swapped
          numbers
          (0 : usize)
          (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)));
      let numbers : (RustSlice u64) ←
        (core_models.slice.Impl.copy_from_slice u64
          numbers
          (← (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec u64 alloc.alloc.Global) swapped)));
      (pure numbers)
    else do
      (pure numbers);
  (pure numbers)

end little_endian_from_slice_u64

