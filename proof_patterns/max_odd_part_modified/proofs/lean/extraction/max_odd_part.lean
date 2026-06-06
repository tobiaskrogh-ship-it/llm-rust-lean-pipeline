
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


namespace max_odd_part

--  Number of trailing zero bits of `x`; `trailing_zeros_u64(0) == 64`.
--  A single shift-and-count `while` loop (see the `trailing_zeros_u64`
--  reference crate). Private here — extracted as a dependency of
--  `max_odd_part`, exactly as in Stein's binary GCD.
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

--  Largest odd part among the integers `1..=n` (`0` when `n == 0`).
-- 
--  Contract:
--  - `max_odd_part(n) <= n` for every `n`;
--  - `max_odd_part(n)` is odd whenever `n >= 1`.
@[spec]
def max_odd_part (n : u64) : RustM u64 := do
  let best : u64 := (0 : u64);
  let i : u64 := (1 : u64);
  let ⟨best, i⟩ ←
    (rust_primitives.hax.while_loop
      (fun ⟨best, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨best, i⟩ => (do (i <=? n) : RustM Bool))
      (fun ⟨best, i⟩ =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      (rust_primitives.hax.Tuple2.mk best i)
      (fun ⟨best, i⟩ =>
        (do
        let r : u32 ← (trailing_zeros_u64 i);
        let odd : u64 ← (i >>>? r);
        let best : u64 ←
          if (← (odd >? best)) then do
            let best : u64 := odd;
            (pure best)
          else do
            (pure best);
        let i : u64 ← (i +? (1 : u64));
        (pure (rust_primitives.hax.Tuple2.mk best i)) :
        RustM (rust_primitives.hax.Tuple2 u64 u64))));
  (pure best)

end max_odd_part

