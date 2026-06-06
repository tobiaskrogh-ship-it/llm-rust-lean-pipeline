
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


namespace array_u64

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

--  Returned on arithmetic overflow or when the total size would exceed
--  `isize::MAX`.
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
def max_size_for_align (align : usize) : RustM usize := do
  ((← ((9223372036854775807 : usize) +? (1 : usize))) -? align)

--  Creates a layout describing the record for a `[u64; n]`.
@[spec]
def array_u64 (n : usize) :
    RustM (core_models.result.Result Layout LayoutError) := do
  let element_size : usize := (8 : usize);
  let align : usize := (8 : usize);
  if
  (← ((← (element_size !=? (0 : usize)))
    &&? (← (n >? (← ((← (max_size_for_align align)) /? element_size)))))) then
  do
    (pure (core_models.result.Result.Err LayoutError.mk))
  else do
    let array_size : usize ← (element_size *? n);
    (pure (core_models.result.Result.Ok
      (Layout.mk (size := array_size) (align := align))))

end array_u64

