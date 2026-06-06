
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


namespace rsplit_array_ref_u64

--  Returns the remaining slice and an array reference to the last `M` items.
-- 
--  Panics if the slice is shorter than `M`.
@[spec]
def split_last_chunk (M : usize) (s : (RustSlice u64)) :
    RustM (rust_primitives.hax.Tuple2 (RustSlice u64) (RustArray u64 M)) := do
  let index : usize ← ((← (core_models.slice.Impl.len u64 s)) -? M);
  let ⟨init, last⟩ ← (core_models.slice.Impl.split_at u64 s index);
  (pure (rust_primitives.hax.Tuple2.mk
    init
    (← (core_models.result.Impl.unwrap
      (RustArray u64 M)
      core_models.array.TryFromSliceError
      (← (core_models.convert.TryInto.try_into
        (RustSlice u64)
        (RustArray u64 M) last))))))

--  Divides one array reference into two at an index from the end.
-- 
--  The first will contain all indices from `[0, N - M)` and the second will
--  contain all indices from `[N - M, N)`.
-- 
--  # Panics
-- 
--  Panics if `M > N`.
@[spec]
def rsplit_array_ref (M : usize) (N : usize) (a : (RustArray u64 N)) :
    RustM (rust_primitives.hax.Tuple2 (RustSlice u64) (RustArray u64 M)) := do
  (split_last_chunk (M) (← (rust_primitives.unsize a)))

end rsplit_array_ref_u64

