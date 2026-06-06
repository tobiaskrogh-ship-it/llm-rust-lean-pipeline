
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

-- Missing prelude declaration: the Hax prelude defines
-- `core_models.num.Impl_9.leading_zeros` and `Impl_9.ilog2` as opaque,
-- but never adds the symmetric `trailing_zeros`. The extraction
-- references it below, so we declare it here as opaque,
-- mirroring `leading_zeros`'s shape.
opaque core_models.num.Impl_9.trailing_zeros (x : u64) : RustM u32

namespace gcd_lcm_u64

@[spec]
def gcd (x : u64) (y : u64) : RustM u64 := do
  let m : u64 := x;
  let n : u64 := y;
  if (← ((← (m ==? (0 : u64))) ||? (← (n ==? (0 : u64))))) then do
    (m |||? n)
  else do
    let shift : u32 ← (core_models.num.Impl_9.trailing_zeros (← (m |||? n)));
    let m : u64 ← (m >>>? (← (core_models.num.Impl_9.trailing_zeros m)));
    let n : u64 ← (n >>>? (← (core_models.num.Impl_9.trailing_zeros n)));
    let ⟨m, n⟩ ←
      (rust_primitives.hax.while_loop
        (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
        (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
        (fun ⟨m, n⟩ =>
          (do
          (rust_primitives.hax.int.from_machine (0 : u32)) :
          RustM hax_lib.int.Int))
        (rust_primitives.hax.Tuple2.mk m n)
        (fun ⟨m, n⟩ =>
          (do
          if (← (m >? n)) then do
            let m : u64 ← (m -? n);
            let m : u64 ←
              (m >>>? (← (core_models.num.Impl_9.trailing_zeros m)));
            (pure (rust_primitives.hax.Tuple2.mk m n))
          else do
            let n : u64 ← (n -? m);
            let n : u64 ←
              (n >>>? (← (core_models.num.Impl_9.trailing_zeros n)));
            (pure (rust_primitives.hax.Tuple2.mk m n)) :
          RustM (rust_primitives.hax.Tuple2 u64 u64))));
    (m <<<? shift)

@[spec]
def gcd_lcm (x : u64) (y : u64) :
    RustM (rust_primitives.hax.Tuple2 u64 u64) := do
  if (← ((← (x ==? (0 : u64))) &&? (← (y ==? (0 : u64))))) then do
    (pure (rust_primitives.hax.Tuple2.mk (0 : u64) (0 : u64)))
  else do
    let g : u64 ← (gcd x y);
    let l : u64 ← (x *? (← (y /? g)));
    (pure (rust_primitives.hax.Tuple2.mk g l))

end gcd_lcm_u64

