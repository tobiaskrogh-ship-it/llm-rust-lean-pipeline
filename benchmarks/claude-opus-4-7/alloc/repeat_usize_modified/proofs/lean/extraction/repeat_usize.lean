
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


namespace repeat_usize

--  Layout of a block of memory: a size and a power-of-two alignment.
structure Layout where
  size : usize
  align : usize

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.clone.Clone Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.marker.Copy Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  core_models.fmt.Debug Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  core_models.marker.StructuralPartialEq Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes Layout Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  core_models.cmp.PartialEq Layout Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6.AssociatedTypes :
  core_models.cmp.Eq.AssociatedTypes Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6 :
  core_models.cmp.Eq Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7.AssociatedTypes :
  core_models.hash.Hash.AssociatedTypes Layout :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7 :
  core_models.hash.Hash Layout :=
  by constructor <;> exact Inhabited.default

@[spec]
def Impl.size (self : Layout) : RustM usize := do (pure (Layout.size self))

@[spec]
def Impl.align (self : Layout) : RustM usize := do (pure (Layout.align self))

--  Returned on arithmetic overflow.
structure LayoutError where
  -- no fields

@[instance] opaque Impl_8.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes LayoutError :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_8 :
  core_models.clone.Clone LayoutError :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_9.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes LayoutError :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_9 :
  core_models.marker.StructuralPartialEq LayoutError :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_10.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes LayoutError LayoutError :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_10 :
  core_models.cmp.PartialEq LayoutError LayoutError :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_11.AssociatedTypes :
  core_models.cmp.Eq.AssociatedTypes LayoutError :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_11 :
  core_models.cmp.Eq LayoutError :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_12.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes LayoutError :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_12 :
  core_models.fmt.Debug LayoutError :=
  by constructor <;> exact Inhabited.default

@[spec]
def size_rounded_up_to_custom_align (size : usize) (align : usize) :
    RustM usize := do
  let align_m1 : usize ← (align -? (1 : usize));
  ((← (size +? align_m1)) &&&? (← (~? align_m1)))

@[spec]
def pad_to_align (layout : Layout) : RustM Layout := do
  let new_size : usize ←
    (size_rounded_up_to_custom_align
      (Layout.size layout)
      (Layout.align layout));
  (pure (Layout.mk (size := new_size) (align := (Layout.align layout))))

@[spec]
def max_size_for_align (align : usize) : RustM usize := do
  ((9223372036854775808 : usize) -? align)

@[spec]
def from_size_alignment (size : usize) (align : usize) :
    RustM (core_models.result.Result Layout LayoutError) := do
  if (← (size >? (← (max_size_for_align align)))) then do
    (pure (core_models.result.Result.Err LayoutError.mk))
  else do
    (pure (core_models.result.Result.Ok
      (Layout.mk (size := size) (align := align))))

@[spec]
def repeat_packed (layout : Layout) (n : usize) :
    RustM (core_models.result.Result Layout LayoutError) := do
  if (← (n ==? (0 : usize))) then do
    (from_size_alignment (0 : usize) (Layout.align layout))
  else do
    if
    (← ((Layout.size layout) >? (← ((18446744073709551615 : usize) /? n)))) then
    do
      (pure (core_models.result.Result.Err LayoutError.mk))
    else do
      (from_size_alignment
        (← ((Layout.size layout) *? n))
        (Layout.align layout))

--  Creates a layout describing the record for `n` instances of `layout`, with
--  suitable padding between each. On success returns `(k, offs)` where `k` is
--  the array layout and `offs` is the stride between elements.
@[spec]
def repeat_layout (layout : Layout) (n : usize) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2 Layout usize)
      LayoutError)
    := do
  let padded : Layout ← (pad_to_align layout);
  match (← (repeat_packed padded n)) with
    | (core_models.result.Result.Ok  repeated) => do
      (pure (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk repeated (← (Impl.size padded)))))
    | _ => do (pure (core_models.result.Result.Err LayoutError.mk))

end repeat_usize

