
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


namespace run_utf8_validation_u8

--  Reimplementation of `core::str::Utf8Error`'s data shape.
structure Utf8Error where
  valid_up_to : usize
  error_len : (core_models.option.Option u8)

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes Utf8Error :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.clone.Clone Utf8Error :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes Utf8Error :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.marker.Copy Utf8Error :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes Utf8Error :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  core_models.marker.StructuralPartialEq Utf8Error :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes Utf8Error Utf8Error :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  core_models.cmp.PartialEq Utf8Error Utf8Error :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes :
  core_models.cmp.Eq.AssociatedTypes Utf8Error :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  core_models.cmp.Eq Utf8Error :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes Utf8Error :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6 :
  core_models.fmt.Debug Utf8Error :=
  by constructor <;> exact Inhabited.default

@[spec]
def Impl.valid_up_to (self : Utf8Error) : RustM usize := do
  (pure (Utf8Error.valid_up_to self))

@[spec]
def Impl.error_len (self : Utf8Error) :
    RustM (core_models.option.Option usize) := do
  match (Utf8Error.error_len self) with
    | (core_models.option.Option.Some  len) => do
      (pure (core_models.option.Option.Some
        (← (rust_primitives.hax.cast_op len : RustM usize))))
    | (core_models.option.Option.None ) => do
      (pure core_models.option.Option.None)

@[spec]
def utf8_char_width (b : u8) : RustM usize := do
  if (← (b <? (128 : u8))) then do
    (pure (1 : usize))
  else do
    if (← (b <? (194 : u8))) then do
      (pure (0 : usize))
    else do
      if (← (b <? (224 : u8))) then do
        (pure (2 : usize))
      else do
        if (← (b <? (240 : u8))) then do
          (pure (3 : usize))
        else do
          if (← (b <? (245 : u8))) then do
            (pure (4 : usize))
          else do
            (pure (0 : usize))

@[spec]
def validate_at (v : (RustSlice u8)) (index : usize) :
    RustM (core_models.result.Result rust_primitives.hax.Tuple0 Utf8Error) := do
  let len : usize ← (core_models.slice.Impl.len u8 v);
  if (← (index >=? len)) then do
    (pure (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk))
  else do
    let old_offset : usize := index;
    let first : u8 ← v[index]_?;
    if (← (first <? (128 : u8))) then do
      (validate_at v (← (index +? (1 : usize))))
    else do
      let w : usize ← (utf8_char_width first);
      if (← (w ==? (2 : usize))) then do
        let i1 : usize ← (index +? (1 : usize));
        if (← (i1 >=? len)) then do
          (pure (core_models.result.Result.Err
            (Utf8Error.mk
              (valid_up_to := old_offset)
              (error_len := core_models.option.Option.None))))
        else do
          if (← ((← ((← v[i1]_?) &&&? (192 : u8))) !=? (128 : u8))) then do
            (pure (core_models.result.Result.Err
              (Utf8Error.mk
                (valid_up_to := old_offset)
                (error_len := (core_models.option.Option.Some (1 : u8))))))
          else do
            (validate_at v (← (i1 +? (1 : usize))))
      else do
        if (← (w ==? (3 : usize))) then do
          let i1 : usize ← (index +? (1 : usize));
          if (← (i1 >=? len)) then do
            (pure (core_models.result.Result.Err
              (Utf8Error.mk
                (valid_up_to := old_offset)
                (error_len := core_models.option.Option.None))))
          else do
            let b2 : u8 ← v[i1]_?;
            let ok2 : Bool ←
              if (← (first ==? (224 : u8))) then do
                ((← (b2 >=? (160 : u8))) &&? (← (b2 <=? (191 : u8))))
              else do
                if
                (← ((← (first >=? (225 : u8))) &&? (← (first <=? (236 : u8)))))
                then do
                  ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (191 : u8))))
                else do
                  if (← (first ==? (237 : u8))) then do
                    ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (159 : u8))))
                  else do
                    if
                    (← ((← (first >=? (238 : u8)))
                      &&? (← (first <=? (239 : u8))))) then do
                      ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (191 : u8))))
                    else do
                      (pure false);
            if (← (!? ok2)) then do
              (pure (core_models.result.Result.Err
                (Utf8Error.mk
                  (valid_up_to := old_offset)
                  (error_len := (core_models.option.Option.Some (1 : u8))))))
            else do
              let i2 : usize ← (i1 +? (1 : usize));
              if (← (i2 >=? len)) then do
                (pure (core_models.result.Result.Err
                  (Utf8Error.mk
                    (valid_up_to := old_offset)
                    (error_len := core_models.option.Option.None))))
              else do
                if
                (← ((← ((← v[i2]_?) &&&? (192 : u8))) !=? (128 : u8))) then do
                  (pure (core_models.result.Result.Err
                    (Utf8Error.mk
                      (valid_up_to := old_offset)
                      (error_len := (core_models.option.Option.Some
                        (2 : u8))))))
                else do
                  (validate_at v (← (i2 +? (1 : usize))))
        else do
          if (← (w ==? (4 : usize))) then do
            let i1 : usize ← (index +? (1 : usize));
            if (← (i1 >=? len)) then do
              (pure (core_models.result.Result.Err
                (Utf8Error.mk
                  (valid_up_to := old_offset)
                  (error_len := core_models.option.Option.None))))
            else do
              let b2 : u8 ← v[i1]_?;
              let ok2 : Bool ←
                if (← (first ==? (240 : u8))) then do
                  ((← (b2 >=? (144 : u8))) &&? (← (b2 <=? (191 : u8))))
                else do
                  if
                  (← ((← (first >=? (241 : u8)))
                    &&? (← (first <=? (243 : u8))))) then do
                    ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (191 : u8))))
                  else do
                    if (← (first ==? (244 : u8))) then do
                      ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (143 : u8))))
                    else do
                      (pure false);
              if (← (!? ok2)) then do
                (pure (core_models.result.Result.Err
                  (Utf8Error.mk
                    (valid_up_to := old_offset)
                    (error_len := (core_models.option.Option.Some (1 : u8))))))
              else do
                let i2 : usize ← (i1 +? (1 : usize));
                if (← (i2 >=? len)) then do
                  (pure (core_models.result.Result.Err
                    (Utf8Error.mk
                      (valid_up_to := old_offset)
                      (error_len := core_models.option.Option.None))))
                else do
                  if
                  (← ((← ((← v[i2]_?) &&&? (192 : u8))) !=? (128 : u8))) then do
                    (pure (core_models.result.Result.Err
                      (Utf8Error.mk
                        (valid_up_to := old_offset)
                        (error_len := (core_models.option.Option.Some
                          (2 : u8))))))
                  else do
                    let i3 : usize ← (i2 +? (1 : usize));
                    if (← (i3 >=? len)) then do
                      (pure (core_models.result.Result.Err
                        (Utf8Error.mk
                          (valid_up_to := old_offset)
                          (error_len := core_models.option.Option.None))))
                    else do
                      if
                      (← ((← ((← v[i3]_?) &&&? (192 : u8))) !=? (128 : u8)))
                      then do
                        (pure (core_models.result.Result.Err
                          (Utf8Error.mk
                            (valid_up_to := old_offset)
                            (error_len := (core_models.option.Option.Some
                              (3 : u8))))))
                      else do
                        (validate_at v (← (i3 +? (1 : usize))))
          else do
            (pure (core_models.result.Result.Err
              (Utf8Error.mk
                (valid_up_to := old_offset)
                (error_len := (core_models.option.Option.Some (1 : u8))))))
partial_fixpoint

@[spec]
def run_utf8_validation (v : (RustSlice u8)) :
    RustM (core_models.result.Result rust_primitives.hax.Tuple0 Utf8Error) := do
  (validate_at v (0 : usize))

end run_utf8_validation_u8

