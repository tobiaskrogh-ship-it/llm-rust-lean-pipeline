
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


namespace pad_to_align_usize

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

@[spec]
def size_rounded_up_to_custom_align (size : usize) (align : usize) :
    RustM usize := do
  let align_m1 : usize ← (align -? (1 : usize));
  ((← (size +? align_m1)) &&&? (← (~? align_m1)))

--  Creates a layout by rounding the size of `layout` up to a multiple of its
--  alignment.
@[spec]
def pad_to_align (layout : Layout) : RustM Layout := do
  let new_size : usize ←
    (size_rounded_up_to_custom_align
      (Layout.size layout)
      (Layout.align layout));
  (pure (Layout.mk (size := new_size) (align := (Layout.align layout))))

end pad_to_align_usize

