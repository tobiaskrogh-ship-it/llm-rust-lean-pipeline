
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


namespace gcd_lcm_u64

@[spec]
def trailing_zeros_u64 (x : u64) : RustM u32 := do
  if (← (x ==? (0 : u64))) then do
    (pure (64 : u32))
  else do
    let y : u64 := x;
    let count : u32 := (0 : u32);
    let ⟨count, y⟩ ←
      (rust_primitives.hax.while_loop
        (fun ⟨count, y⟩ => (do (pure true) : RustM Bool))
        (fun ⟨count, y⟩ =>
          (do ((← (y &&&? (1 : u64))) ==? (0 : u64)) : RustM Bool))
        (fun ⟨count, y⟩ =>
          (do
          (rust_primitives.hax.int.from_machine (0 : u32)) :
          RustM hax_lib.int.Int))
        (rust_primitives.hax.Tuple2.mk count y)
        (fun ⟨count, y⟩ =>
          (do
          let y : u64 ← (y >>>? (1 : i32));
          let count : u32 ← (count +? (1 : u32));
          (pure (rust_primitives.hax.Tuple2.mk count y)) :
          RustM (rust_primitives.hax.Tuple2 u32 u64))));
    (pure count)

@[spec]
def gcd_stein_loop (m : u64) (n : u64) : RustM u64 := do
  if (← (m ==? n)) then do
    (pure m)
  else do
    if (← (m >? n)) then do
      let d : u64 ← (m -? n);
      (gcd_stein_loop (← (d >>>? (← (trailing_zeros_u64 d)))) n)
    else do
      let d : u64 ← (n -? m);
      (gcd_stein_loop m (← (d >>>? (← (trailing_zeros_u64 d)))))
partial_fixpoint

@[spec]
def gcd (x : u64) (y : u64) : RustM u64 := do
  let m : u64 := x;
  let n : u64 := y;
  if (← ((← (m ==? (0 : u64))) ||? (← (n ==? (0 : u64))))) then do
    (m |||? n)
  else do
    let shift : u32 ← (trailing_zeros_u64 (← (m |||? n)));
    let m : u64 ← (m >>>? (← (trailing_zeros_u64 m)));
    let n : u64 ← (n >>>? (← (trailing_zeros_u64 n)));
    ((← (gcd_stein_loop m n)) <<<? shift)

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

