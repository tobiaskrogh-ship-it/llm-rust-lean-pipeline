
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


namespace clever_143_order_by_points

--  HumanEval/145 / CLEVER 143 — `order_by_points(nums)`.  Stable-sort
--  `nums` ascending by the sum of their signed digits (where for
--  negative `n`, the first digit takes the sign).  Ties preserve the
--  original order.
@[spec]
def first_digit_at (n : i64) : RustM i64 := do
  if (← (n <? (10 : i64))) then do
    (pure n)
  else do
    (first_digit_at (← (n /? (10 : i64))))
partial_fixpoint

@[spec]
def digit_sum_at (n : i64) (acc : i64) : RustM i64 := do
  if (← (n ==? (0 : i64))) then do
    (pure acc)
  else do
    (digit_sum_at (← (n /? (10 : i64))) (← (acc +? (← (n %? (10 : i64))))))
partial_fixpoint

@[spec]
def signed_digit_sum (n : i64) : RustM i64 := do
  if (← (n ==? (0 : i64))) then do
    (pure (0 : i64))
  else do
    if (← (n >? (0 : i64))) then do
      (digit_sum_at n (0 : i64))
    else do
      let m : i64 ← (-? n);
      ((← (digit_sum_at m (0 : i64)))
        -? (← ((2 : i64) *? (← (first_digit_at m)))))

@[spec]
def insert_stable_at
    (v : (alloc.vec.Vec i64 alloc.alloc.Global))
    (x : i64)
    (kx : i64)
    (i : usize)
    (done : Bool)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (alloc.vec.Impl_1.len i64 alloc.alloc.Global v)))) then do
    if done then do
      (pure acc)
    else do
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[x]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (pure acc)
  else do
    let vi : i64 ← v[i]_?;
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
    if (← ((← (!? done)) &&? (← ((← (signed_digit_sum vi)) >? kx)))) then do
      let chunk : (RustArray i64 2) := (RustArray.ofVec #v[x, vi]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (insert_stable_at v x kx (← (i +? (1 : usize))) true acc)
    else do
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[vi]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (insert_stable_at v x kx (← (i +? (1 : usize))) done acc)
partial_fixpoint

@[spec]
def insert_stable (v : (alloc.vec.Vec i64 alloc.alloc.Global)) (x : i64) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  let kx : i64 ← (signed_digit_sum x);
  (insert_stable_at
    v
    x
    kx
    (0 : usize)
    false
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

@[spec]
def sort_at
    (l : (RustSlice i64))
    (i : usize)
    (s : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure s)
  else do
    (sort_at l (← (i +? (1 : usize))) (← (insert_stable s (← l[i]_?))))
partial_fixpoint

@[spec]
def order_by_points (nums : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  (sort_at
    nums
    (0 : usize)
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_143_order_by_points

