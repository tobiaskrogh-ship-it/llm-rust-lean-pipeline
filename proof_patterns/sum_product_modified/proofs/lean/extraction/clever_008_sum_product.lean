
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


namespace clever_008_sum_product

--  For a given list of integers, return a tuple of (sum, product).
--  Empty sum is 0; empty product is 1.
@[spec]
def sum_product_at
    (numbers : (RustSlice i64))
    (i : usize)
    (sum : i64)
    (product : i64) :
    RustM (rust_primitives.hax.Tuple2 i64 i64) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 numbers)))) then do
    (pure (rust_primitives.hax.Tuple2.mk sum product))
  else do
    (sum_product_at
      numbers
      (← (i +? (1 : usize)))
      (← (sum +? (← numbers[i]_?)))
      (← (product *? (← numbers[i]_?))))
partial_fixpoint

@[spec]
def sum_product (numbers : (RustSlice i64)) :
    RustM (rust_primitives.hax.Tuple2 i64 i64) := do
  (sum_product_at numbers (0 : usize) (0 : i64) (1 : i64))

end clever_008_sum_product

