
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


namespace from_size_align_usize

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

--  The minimum size in bytes for a memory block of this layout.
@[spec]
def Impl.size (self : Layout) : RustM usize := do (pure (Layout.size self))

--  The minimum byte alignment for a memory block of this layout.
@[spec]
def Impl.align (self : Layout) : RustM usize := do (pure (Layout.align self))

--  Returned when the parameters given to `from_size_align` do not satisfy its
--  documented constraints.
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
def is_power_of_two_usize (x : usize) : RustM Bool := do
  ((← (x !=? (0 : usize)))
    &&? (← ((← (x &&&? (← (x -? (1 : usize))))) ==? (0 : usize))))

@[spec]
def max_size_for_align (align : usize) : RustM usize := do
  ((← ((9223372036854775807 : usize) +? (1 : usize))) -? align)

@[spec]
def is_size_align_valid (size : usize) (align : usize) : RustM Bool := do
  if (← (!? (← (is_power_of_two_usize align)))) then do
    (pure false)
  else do
    if (← (size >? (← (max_size_for_align align)))) then do
      (pure false)
    else do
      (pure true)

--  Constructs a `Layout` from a given `size` and `align`, or returns
--  `LayoutError` if `align` is not a power of two, or `size` rounded up to a
--  multiple of `align` would overflow `isize`.
@[spec]
def from_size_align (size : usize) (align : usize) :
    RustM (core_models.result.Result Layout LayoutError) := do
  if (← (is_size_align_valid size align)) then do
    (pure (core_models.result.Result.Ok
      (Layout.mk (size := size) (align := align))))
  else do
    (pure (core_models.result.Result.Err LayoutError.mk))

end from_size_align_usize

