
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


namespace byteorder.io

--  Convert a slice of T (where T is plain old data) to its mutable binary
--  representation.
-- 
--  This function is wildly unsafe because it permits arbitrary modification of
--  the binary representation of any `Copy` type. Use with care. It's intended
--  to be called only where `T` is a numeric type.
@[spec]
def slice_to_u8_mut
    (T : Type)
    [trait_constr_slice_to_u8_mut_associated_type_i0 :
      core_models.marker.Copy.AssociatedTypes
      T]
    [trait_constr_slice_to_u8_mut_i0 : core_models.marker.Copy T ]
    (slice : (RustSlice T)) :
    RustM sorry := do
  (pure sorry)

end byteorder.io


namespace byteorder

@[spec]
def extend_sign (val : u64) (nbytes : usize) : RustM i64 := do
  let shift : usize ← ((← ((8 : usize) -? nbytes)) *? (8 : usize));
  ((← (rust_primitives.hax.cast_op (← (val <<<? shift)) : RustM i64))
    >>>? shift)

@[spec]
def extend_sign128 (val : u128) (nbytes : usize) : RustM i128 := do
  let shift : usize ← ((← ((16 : usize) -? nbytes)) *? (8 : usize));
  ((← (rust_primitives.hax.cast_op (← (val <<<? shift)) : RustM i128))
    >>>? shift)

@[spec]
def unextend_sign (val : i64) (nbytes : usize) : RustM u64 := do
  let shift : usize ← ((← ((8 : usize) -? nbytes)) *? (8 : usize));
  ((← (rust_primitives.hax.cast_op (← (val <<<? shift)) : RustM u64))
    >>>? shift)

@[spec]
def unextend_sign128 (val : i128) (nbytes : usize) : RustM u128 := do
  let shift : usize ← ((← ((16 : usize) -? nbytes)) *? (8 : usize));
  ((← (rust_primitives.hax.cast_op (← (val <<<? shift)) : RustM u128))
    >>>? shift)

@[spec]
def pack_size (n : u64) : RustM usize := do
  if (← (n <? (← ((1 : u64) <<<? (8 : i32))))) then do
    (pure (1 : usize))
  else do
    if (← (n <? (← ((1 : u64) <<<? (16 : i32))))) then do
      (pure (2 : usize))
    else do
      if (← (n <? (← ((1 : u64) <<<? (24 : i32))))) then do
        (pure (3 : usize))
      else do
        if (← (n <? (← ((1 : u64) <<<? (32 : i32))))) then do
          (pure (4 : usize))
        else do
          if (← (n <? (← ((1 : u64) <<<? (40 : i32))))) then do
            (pure (5 : usize))
          else do
            if (← (n <? (← ((1 : u64) <<<? (48 : i32))))) then do
              (pure (6 : usize))
            else do
              if (← (n <? (← ((1 : u64) <<<? (56 : i32))))) then do
                (pure (7 : usize))
              else do
                (pure (8 : usize))

@[spec]
def pack_size128 (n : u128) : RustM usize := do
  if (← (n <? (← ((1 : u128) <<<? (8 : i32))))) then do
    (pure (1 : usize))
  else do
    if (← (n <? (← ((1 : u128) <<<? (16 : i32))))) then do
      (pure (2 : usize))
    else do
      if (← (n <? (← ((1 : u128) <<<? (24 : i32))))) then do
        (pure (3 : usize))
      else do
        if (← (n <? (← ((1 : u128) <<<? (32 : i32))))) then do
          (pure (4 : usize))
        else do
          if (← (n <? (← ((1 : u128) <<<? (40 : i32))))) then do
            (pure (5 : usize))
          else do
            if (← (n <? (← ((1 : u128) <<<? (48 : i32))))) then do
              (pure (6 : usize))
            else do
              if (← (n <? (← ((1 : u128) <<<? (56 : i32))))) then do
                (pure (7 : usize))
              else do
                if (← (n <? (← ((1 : u128) <<<? (64 : i32))))) then do
                  (pure (8 : usize))
                else do
                  if (← (n <? (← ((1 : u128) <<<? (72 : i32))))) then do
                    (pure (9 : usize))
                  else do
                    if (← (n <? (← ((1 : u128) <<<? (80 : i32))))) then do
                      (pure (10 : usize))
                    else do
                      if (← (n <? (← ((1 : u128) <<<? (88 : i32))))) then do
                        (pure (11 : usize))
                      else do
                        if (← (n <? (← ((1 : u128) <<<? (96 : i32))))) then do
                          (pure (12 : usize))
                        else do
                          if
                          (← (n <? (← ((1 : u128) <<<? (104 : i32))))) then do
                            (pure (13 : usize))
                          else do
                            if
                            (← (n <? (← ((1 : u128) <<<? (112 : i32))))) then do
                              (pure (14 : usize))
                            else do
                              if
                              (← (n <? (← ((1 : u128) <<<? (120 : i32))))) then
                              do
                                (pure (15 : usize))
                              else do
                                (pure (16 : usize))

end byteorder


namespace byteorder.private

--  Sealed stops crates other than byteorder from implementing any traits
--  that use it.
class Sealed.AssociatedTypes (Self : Type) where

class Sealed (Self : Type)
  [associatedTypes : outParam (Sealed.AssociatedTypes (Self : Type))]
  where

end byteorder.private


namespace byteorder

def ByteOrder.read_f32_into._ : rust_primitives.hax.Tuple0 :=
  RustM.of_isOk
    (do
    (hax_lib.assert
      (← ((← (core_models.mem.align_of u32 rust_primitives.hax.Tuple0.mk))
        <=? (← (core_models.mem.align_of f32 rust_primitives.hax.Tuple0.mk))))))
    (by rfl)

def ByteOrder.read_f64_into._ : rust_primitives.hax.Tuple0 :=
  RustM.of_isOk
    (do
    (hax_lib.assert
      (← ((← (core_models.mem.align_of u64 rust_primitives.hax.Tuple0.mk))
        <=? (← (core_models.mem.align_of f64 rust_primitives.hax.Tuple0.mk))))))
    (by rfl)

--  Defines big-endian serialization.
-- 
--  Note that this type has no value constructor. It is used purely at the
--  type level.
-- 
--  # Examples
-- 
--  Write and read `u32` numbers in big endian order:
-- 
--  ```rust
--  use byteorder::{ByteOrder, BigEndian};
-- 
--  let mut buf = [0; 4];
--  BigEndian::write_u32(&mut buf, 1_000_000);
--  assert_eq!(1_000_000, BigEndian::read_u32(&buf));
--  ```
inductive BigEndian : Type


end byteorder


namespace byteorder.private

@[reducible] instance Impl_1.AssociatedTypes :
  Sealed.AssociatedTypes byteorder.BigEndian
  where

instance Impl_1 : Sealed byteorder.BigEndian where

end byteorder.private


namespace byteorder

@[spec]
def BigEndian_cast_to_repr (x : BigEndian) :
    RustM rust_primitives.hax.Never := do
  match x with 

@[instance] opaque Impl_4.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  core_models.clone.Clone BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  core_models.marker.Copy BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6 :
  core_models.fmt.Debug BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_8.AssociatedTypes :
  core_models.hash.Hash.AssociatedTypes BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_8 :
  core_models.hash.Hash BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_10.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_10 :
  core_models.marker.StructuralPartialEq BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_11.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes BigEndian BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_11 :
  core_models.cmp.PartialEq BigEndian BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7.AssociatedTypes :
  core_models.cmp.Eq.AssociatedTypes BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7 :
  core_models.cmp.Eq BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_12.AssociatedTypes :
  core_models.cmp.PartialOrd.AssociatedTypes BigEndian BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_12 :
  core_models.cmp.PartialOrd BigEndian BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_9.AssociatedTypes :
  core_models.cmp.Ord.AssociatedTypes BigEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_9 :
  core_models.cmp.Ord BigEndian :=
  by constructor <;> exact Inhabited.default

@[reducible] instance Impl.AssociatedTypes :
  core_models.default.Default.AssociatedTypes BigEndian
  where

instance Impl : core_models.default.Default BigEndian where
  default := fun (_ : rust_primitives.hax.Tuple0) => do
    (rust_primitives.hax.never_to_any
      (← (core_models.panicking.panic_fmt
        (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
          (RustArray.ofVec #v["BigEndian default"]))))))

--  A type alias for [`BigEndian`].
-- 
--  [`BigEndian`]: enum.BigEndian.html
abbrev BE : Type := BigEndian

--  Defines little-endian serialization.
-- 
--  Note that this type has no value constructor. It is used purely at the
--  type level.
-- 
--  # Examples
-- 
--  Write and read `u32` numbers in little endian order:
-- 
--  ```rust
--  use byteorder::{ByteOrder, LittleEndian};
-- 
--  let mut buf = [0; 4];
--  LittleEndian::write_u32(&mut buf, 1_000_000);
--  assert_eq!(1_000_000, LittleEndian::read_u32(&buf));
--  ```
inductive LittleEndian : Type


end byteorder


namespace byteorder.private

@[reducible] instance Impl.AssociatedTypes :
  Sealed.AssociatedTypes byteorder.LittleEndian
  where

instance Impl : Sealed byteorder.LittleEndian where

end byteorder.private


namespace byteorder

@[spec]
def LittleEndian_cast_to_repr (x : LittleEndian) :
    RustM rust_primitives.hax.Never := do
  match x with 

@[instance] opaque Impl_13.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_13 :
  core_models.clone.Clone LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_14.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_14 :
  core_models.marker.Copy LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_15.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_15 :
  core_models.fmt.Debug LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_17.AssociatedTypes :
  core_models.hash.Hash.AssociatedTypes LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_17 :
  core_models.hash.Hash LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_19.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_19 :
  core_models.marker.StructuralPartialEq LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_20.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes LittleEndian LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_20 :
  core_models.cmp.PartialEq LittleEndian LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_16.AssociatedTypes :
  core_models.cmp.Eq.AssociatedTypes LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_16 :
  core_models.cmp.Eq LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_21.AssociatedTypes :
  core_models.cmp.PartialOrd.AssociatedTypes LittleEndian LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_21 :
  core_models.cmp.PartialOrd LittleEndian LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_18.AssociatedTypes :
  core_models.cmp.Ord.AssociatedTypes LittleEndian :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_18 :
  core_models.cmp.Ord LittleEndian :=
  by constructor <;> exact Inhabited.default

@[reducible] instance Impl_1.AssociatedTypes :
  core_models.default.Default.AssociatedTypes LittleEndian
  where

instance Impl_1 : core_models.default.Default LittleEndian where
  default := fun (_ : rust_primitives.hax.Tuple0) => do
    (rust_primitives.hax.never_to_any
      (← (core_models.panicking.panic_fmt
        (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
          (RustArray.ofVec #v["LittleEndian default"]))))))

--  A type alias for [`LittleEndian`].
-- 
--  [`LittleEndian`]: enum.LittleEndian.html
abbrev LE : Type := LittleEndian

--  Defines network byte order serialization.
-- 
--  Network byte order is defined by [RFC 1700][1] to be big-endian, and is
--  referred to in several protocol specifications.  This type is an alias of
--  [`BigEndian`].
-- 
--  [1]: https://tools.ietf.org/html/rfc1700
-- 
--  Note that this type has no value constructor. It is used purely at the
--  type level.
-- 
--  # Examples
-- 
--  Write and read `i16` numbers in big endian order:
-- 
--  ```rust
--  use byteorder::{ByteOrder, NetworkEndian, BigEndian};
-- 
--  let mut buf = [0; 2];
--  BigEndian::write_i16(&mut buf, -5_000);
--  assert_eq!(-5_000, NetworkEndian::read_i16(&buf));
--  ```
-- 
--  [`BigEndian`]: enum.BigEndian.html
abbrev NetworkEndian : Type := BigEndian

--  Defines system native-endian serialization.
-- 
--  Note that this type has no value constructor. It is used purely at the
--  type level.
-- 
--  On this platform, this is an alias for [`LittleEndian`].
-- 
--  [`LittleEndian`]: enum.LittleEndian.html
abbrev NativeEndian : Type := LittleEndian

def Impl_2.read_u16_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u16 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_2.read_u32_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u32 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_2.read_u64_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u64 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_2.read_u128_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u128 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_2.write_u16_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u16 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_2.write_u32_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u32 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_2.write_u64_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u64 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_2.write_u128_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u128 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_3.read_u16_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u16 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_3.read_u32_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u32 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_3.read_u64_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u64 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_3.read_u128_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u128 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_3.write_u16_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u16 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_3.write_u32_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u32 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_3.write_u64_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u64 rust_primitives.hax.Tuple0.mk))
    (by rfl)

def Impl_3.write_u128_into.SIZE : usize :=
  RustM.of_isOk
    (do (core_models.mem.size_of u128 rust_primitives.hax.Tuple0.mk))
    (by rfl)

--  `ByteOrder` describes types that can serialize integers as bytes.
-- 
--  Note that `Self` does not appear anywhere in this trait's definition!
--  Therefore, in order to use it, you'll need to use syntax like
--  `T::read_u16(&[0, 1])` where `T` implements `ByteOrder`.
-- 
--  This crate provides two types that implement `ByteOrder`: [`BigEndian`]
--  and [`LittleEndian`].
--  This trait is sealed and cannot be implemented for callers to avoid
--  breaking backwards compatibility when adding new derived traits.
-- 
--  # Examples
-- 
--  Write and read `u32` numbers in little endian order:
-- 
--  ```rust
--  use byteorder::{ByteOrder, LittleEndian};
-- 
--  let mut buf = [0; 4];
--  LittleEndian::write_u32(&mut buf, 1_000_000);
--  assert_eq!(1_000_000, LittleEndian::read_u32(&buf));
--  ```
-- 
--  Write and read `i16` numbers in big endian order:
-- 
--  ```rust
--  use byteorder::{ByteOrder, BigEndian};
-- 
--  let mut buf = [0; 2];
--  BigEndian::write_i16(&mut buf, -5_000);
--  assert_eq!(-5_000, BigEndian::read_i16(&buf));
--  ```
-- 
--  [`BigEndian`]: enum.BigEndian.html
--  [`LittleEndian`]: enum.LittleEndian.html
class ByteOrder.AssociatedTypes (Self : Type) where
  [trait_constr_ByteOrder_i0 : core_models.clone.Clone.AssociatedTypes Self]
  [trait_constr_ByteOrder_i1 : core_models.marker.Copy.AssociatedTypes Self]
  [trait_constr_ByteOrder_i2 : core_models.fmt.Debug.AssociatedTypes Self]
  [trait_constr_ByteOrder_i3 : core_models.default.Default.AssociatedTypes Self]
  [trait_constr_ByteOrder_i4 : core_models.cmp.Eq.AssociatedTypes Self]
  [trait_constr_ByteOrder_i5 : core_models.hash.Hash.AssociatedTypes Self]
  [trait_constr_ByteOrder_i6 : core_models.cmp.Ord.AssociatedTypes Self]
  [trait_constr_ByteOrder_i7 :
  core_models.cmp.PartialEq.AssociatedTypes
  Self
  Self]
  [trait_constr_ByteOrder_i8 :
  core_models.cmp.PartialOrd.AssociatedTypes
  Self
  Self]
  [trait_constr_ByteOrder_i9 : byteorder.private.Sealed.AssociatedTypes Self]

attribute [instance_reducible, instance]
  ByteOrder.AssociatedTypes.trait_constr_ByteOrder_i0

attribute [instance_reducible, instance]
  ByteOrder.AssociatedTypes.trait_constr_ByteOrder_i1

attribute [instance_reducible, instance]
  ByteOrder.AssociatedTypes.trait_constr_ByteOrder_i2

attribute [instance_reducible, instance]
  ByteOrder.AssociatedTypes.trait_constr_ByteOrder_i3

attribute [instance_reducible, instance]
  ByteOrder.AssociatedTypes.trait_constr_ByteOrder_i4

attribute [instance_reducible, instance]
  ByteOrder.AssociatedTypes.trait_constr_ByteOrder_i5

attribute [instance_reducible, instance]
  ByteOrder.AssociatedTypes.trait_constr_ByteOrder_i6

attribute [instance_reducible, instance]
  ByteOrder.AssociatedTypes.trait_constr_ByteOrder_i7

attribute [instance_reducible, instance]
  ByteOrder.AssociatedTypes.trait_constr_ByteOrder_i8

attribute [instance_reducible, instance]
  ByteOrder.AssociatedTypes.trait_constr_ByteOrder_i9

class ByteOrder (Self : Type)
  [associatedTypes : outParam (ByteOrder.AssociatedTypes (Self : Type))]
  where
  [trait_constr_ByteOrder_i0 : core_models.clone.Clone Self]
  [trait_constr_ByteOrder_i1 : core_models.marker.Copy Self]
  [trait_constr_ByteOrder_i2 : core_models.fmt.Debug Self]
  [trait_constr_ByteOrder_i3 : core_models.default.Default Self]
  [trait_constr_ByteOrder_i4 : core_models.cmp.Eq Self]
  [trait_constr_ByteOrder_i5 : core_models.hash.Hash Self]
  [trait_constr_ByteOrder_i6 : core_models.cmp.Ord Self]
  [trait_constr_ByteOrder_i7 : core_models.cmp.PartialEq Self Self]
  [trait_constr_ByteOrder_i8 : core_models.cmp.PartialOrd Self Self]
  [trait_constr_ByteOrder_i9 : byteorder.private.Sealed Self]
  read_u16 (Self) : ((RustSlice u8) -> RustM u16)
  read_u24 (Self) (buf : (RustSlice u8)) :RustM u32 := do
    (rust_primitives.hax.cast_op
      (← (ByteOrder.read_uint Self buf (3 : usize))) :
      RustM u32)
  read_u32 (Self) : ((RustSlice u8) -> RustM u32)
  read_u48 (Self) (buf : (RustSlice u8)) :RustM u64 := do
    (ByteOrder.read_uint Self buf (6 : usize))
  read_u64 (Self) : ((RustSlice u8) -> RustM u64)
  read_u128 (Self) : ((RustSlice u8) -> RustM u128)
  read_uint (Self) : ((RustSlice u8) -> usize -> RustM u64)
  read_uint128 (Self) : ((RustSlice u8) -> usize -> RustM u128)
  write_u16 (Self) : ((RustSlice u8) -> u16 -> RustM (RustSlice u8))
  write_u24 (Self) (buf : (RustSlice u8)) (n : u32) :RustM (RustSlice u8) := do
    let buf : (RustSlice u8) ←
      (ByteOrder.write_uint
        Self buf (← (rust_primitives.hax.cast_op n : RustM u64)) (3 : usize));
    (pure buf)
  write_u32 (Self) : ((RustSlice u8) -> u32 -> RustM (RustSlice u8))
  write_u48 (Self) (buf : (RustSlice u8)) (n : u64) :RustM (RustSlice u8) := do
    let buf : (RustSlice u8) ← (ByteOrder.write_uint Self buf n (6 : usize));
    (pure buf)
  write_u64 (Self) : ((RustSlice u8) -> u64 -> RustM (RustSlice u8))
  write_u128 (Self) : ((RustSlice u8) -> u128 -> RustM (RustSlice u8))
  write_uint (Self) : ((RustSlice u8) -> u64 -> usize -> RustM (RustSlice u8))
  write_uint128 (Self) :
    ((RustSlice u8) -> u128 -> usize -> RustM (RustSlice u8))
  read_i16 (Self) (buf : (RustSlice u8)) :RustM i16 := do
    (rust_primitives.hax.cast_op (← (ByteOrder.read_u16 Self buf)) : RustM i16)
  read_i24 (Self) (buf : (RustSlice u8)) :RustM i32 := do
    (rust_primitives.hax.cast_op
      (← (ByteOrder.read_int Self buf (3 : usize))) :
      RustM i32)
  read_i32 (Self) (buf : (RustSlice u8)) :RustM i32 := do
    (rust_primitives.hax.cast_op (← (ByteOrder.read_u32 Self buf)) : RustM i32)
  read_i48 (Self) (buf : (RustSlice u8)) :RustM i64 := do
    (ByteOrder.read_int Self buf (6 : usize))
  read_i64 (Self) (buf : (RustSlice u8)) :RustM i64 := do
    (rust_primitives.hax.cast_op (← (ByteOrder.read_u64 Self buf)) : RustM i64)
  read_i128 (Self) (buf : (RustSlice u8)) :RustM i128 := do
    (rust_primitives.hax.cast_op
      (← (ByteOrder.read_u128 Self buf)) :
      RustM i128)
  read_int (Self) (buf : (RustSlice u8)) (nbytes : usize) :RustM i64 := do
    (extend_sign (← (ByteOrder.read_uint Self buf nbytes)) nbytes)
  read_int128 (Self) (buf : (RustSlice u8)) (nbytes : usize) :RustM i128 := do
    (extend_sign128 (← (ByteOrder.read_uint128 Self buf nbytes)) nbytes)
  read_f32 (Self) (buf : (RustSlice u8)) :RustM f32 := do
    (core_models.f32.Impl.from_bits (← (ByteOrder.read_u32 Self buf)))
  read_f64 (Self) (buf : (RustSlice u8)) :RustM f64 := do
    (core_models.f64.Impl.from_bits (← (ByteOrder.read_u64 Self buf)))
  write_i16 (Self) (buf : (RustSlice u8)) (n : i16) :RustM (RustSlice u8) := do
    let buf : (RustSlice u8) ←
      (ByteOrder.write_u16
        Self buf (← (rust_primitives.hax.cast_op n : RustM u16)));
    (pure buf)
  write_i24 (Self) (buf : (RustSlice u8)) (n : i32) :RustM (RustSlice u8) := do
    let buf : (RustSlice u8) ←
      (ByteOrder.write_int
        Self buf (← (rust_primitives.hax.cast_op n : RustM i64)) (3 : usize));
    (pure buf)
  write_i32 (Self) (buf : (RustSlice u8)) (n : i32) :RustM (RustSlice u8) := do
    let buf : (RustSlice u8) ←
      (ByteOrder.write_u32
        Self buf (← (rust_primitives.hax.cast_op n : RustM u32)));
    (pure buf)
  write_i48 (Self) (buf : (RustSlice u8)) (n : i64) :RustM (RustSlice u8) := do
    let buf : (RustSlice u8) ← (ByteOrder.write_int Self buf n (6 : usize));
    (pure buf)
  write_i64 (Self) (buf : (RustSlice u8)) (n : i64) :RustM (RustSlice u8) := do
    let buf : (RustSlice u8) ←
      (ByteOrder.write_u64
        Self buf (← (rust_primitives.hax.cast_op n : RustM u64)));
    (pure buf)
  write_i128 (Self) (buf : (RustSlice u8)) (n : i128) :RustM (RustSlice u8) :=
    do
    let buf : (RustSlice u8) ←
      (ByteOrder.write_u128
        Self buf (← (rust_primitives.hax.cast_op n : RustM u128)));
    (pure buf)
  write_int (Self) (buf : (RustSlice u8)) (n : i64) (nbytes : usize) :RustM
    (RustSlice u8) := do
    let buf : (RustSlice u8) ←
      (ByteOrder.write_uint Self buf (← (unextend_sign n nbytes)) nbytes);
    (pure buf)
  write_int128 (Self) (buf : (RustSlice u8)) (n : i128) (nbytes : usize) :RustM
    (RustSlice u8) := do
    let buf : (RustSlice u8) ←
      (ByteOrder.write_uint128 Self buf (← (unextend_sign128 n nbytes)) nbytes);
    (pure buf)
  write_f32 (Self) (buf : (RustSlice u8)) (n : f32) :RustM (RustSlice u8) := do
    let buf : (RustSlice u8) ←
      (ByteOrder.write_u32 Self buf (← (core_models.f32.Impl.to_bits n)));
    (pure buf)
  write_f64 (Self) (buf : (RustSlice u8)) (n : f64) :RustM (RustSlice u8) := do
    let buf : (RustSlice u8) ←
      (ByteOrder.write_u64 Self buf (← (core_models.f64.Impl.to_bits n)));
    (pure buf)
  read_u16_into (Self) :
    ((RustSlice u8) -> (RustSlice u16) -> RustM (RustSlice u16))
  read_u32_into (Self) :
    ((RustSlice u8) -> (RustSlice u32) -> RustM (RustSlice u32))
  read_u64_into (Self) :
    ((RustSlice u8) -> (RustSlice u64) -> RustM (RustSlice u64))
  read_u128_into (Self) :
    ((RustSlice u8) -> (RustSlice u128) -> RustM (RustSlice u128))
  read_i16_into (Self) (src : (RustSlice u8)) (dst : (RustSlice i16)) :RustM
    rust_primitives.hax.Tuple0 := do
    (pure sorry)
  read_i32_into (Self) (src : (RustSlice u8)) (dst : (RustSlice i32)) :RustM
    rust_primitives.hax.Tuple0 := do
    (pure sorry)
  read_i64_into (Self) (src : (RustSlice u8)) (dst : (RustSlice i64)) :RustM
    rust_primitives.hax.Tuple0 := do
    (pure sorry)
  read_i128_into (Self) (src : (RustSlice u8)) (dst : (RustSlice i128)) :RustM
    rust_primitives.hax.Tuple0 := do
    (pure sorry)
  read_f32_into (Self) (src : (RustSlice u8)) (dst : (RustSlice f32)) :RustM
    rust_primitives.hax.Tuple0 := do
    (pure sorry)
  read_f32_into_unchecked (Self) (src : (RustSlice u8)) (dst : (RustSlice f32))
    :RustM (RustSlice f32) := do
    let dst : (RustSlice f32) ← (ByteOrder.read_f32_into Self src dst);
    (pure dst)
  read_f64_into (Self) (src : (RustSlice u8)) (dst : (RustSlice f64)) :RustM
    rust_primitives.hax.Tuple0 := do
    (pure sorry)
  read_f64_into_unchecked (Self) (src : (RustSlice u8)) (dst : (RustSlice f64))
    :RustM (RustSlice f64) := do
    let dst : (RustSlice f64) ← (ByteOrder.read_f64_into Self src dst);
    (pure dst)
  write_u16_into (Self) :
    ((RustSlice u16) -> (RustSlice u8) -> RustM (RustSlice u8))
  write_u32_into (Self) :
    ((RustSlice u32) -> (RustSlice u8) -> RustM (RustSlice u8))
  write_u64_into (Self) :
    ((RustSlice u64) -> (RustSlice u8) -> RustM (RustSlice u8))
  write_u128_into (Self) :
    ((RustSlice u128) -> (RustSlice u8) -> RustM (RustSlice u8))
  write_i8_into (Self) (src : (RustSlice i8)) (dst : (RustSlice u8)) :RustM
    (RustSlice u8) := do
    let src : (RustSlice u8) := sorry;
    let dst : (RustSlice u8) ←
      (core_models.slice.Impl.copy_from_slice u8 dst src);
    (pure dst)
  write_i16_into (Self) (src : (RustSlice i16)) (dst : (RustSlice u8)) :RustM
    (RustSlice u8) := do
    let src : (RustSlice u16) := sorry;
    let dst : (RustSlice u8) ← (ByteOrder.write_u16_into Self src dst);
    (pure dst)
  write_i32_into (Self) (src : (RustSlice i32)) (dst : (RustSlice u8)) :RustM
    (RustSlice u8) := do
    let src : (RustSlice u32) := sorry;
    let dst : (RustSlice u8) ← (ByteOrder.write_u32_into Self src dst);
    (pure dst)
  write_i64_into (Self) (src : (RustSlice i64)) (dst : (RustSlice u8)) :RustM
    (RustSlice u8) := do
    let src : (RustSlice u64) := sorry;
    let dst : (RustSlice u8) ← (ByteOrder.write_u64_into Self src dst);
    (pure dst)
  write_i128_into (Self) (src : (RustSlice i128)) (dst : (RustSlice u8)) :RustM
    (RustSlice u8) := do
    let src : (RustSlice u128) := sorry;
    let dst : (RustSlice u8) ← (ByteOrder.write_u128_into Self src dst);
    (pure dst)
  write_f32_into (Self) (src : (RustSlice f32)) (dst : (RustSlice u8)) :RustM
    (RustSlice u8) := do
    let src : (RustSlice u32) := sorry;
    let dst : (RustSlice u8) ← (ByteOrder.write_u32_into Self src dst);
    (pure dst)
  write_f64_into (Self) (src : (RustSlice f64)) (dst : (RustSlice u8)) :RustM
    (RustSlice u8) := do
    let src : (RustSlice u64) := sorry;
    let dst : (RustSlice u8) ← (ByteOrder.write_u64_into Self src dst);
    (pure dst)
  from_slice_u16 (Self) : ((RustSlice u16) -> RustM (RustSlice u16))
  from_slice_u32 (Self) : ((RustSlice u32) -> RustM (RustSlice u32))
  from_slice_u64 (Self) : ((RustSlice u64) -> RustM (RustSlice u64))
  from_slice_u128 (Self) : ((RustSlice u128) -> RustM (RustSlice u128))
  from_slice_i16 (Self) (src : (RustSlice i16)) :RustM
    rust_primitives.hax.Tuple0 := do
    (pure sorry)
  from_slice_i32 (Self) (src : (RustSlice i32)) :RustM
    rust_primitives.hax.Tuple0 := do
    (pure sorry)
  from_slice_i64 (Self) (src : (RustSlice i64)) :RustM
    rust_primitives.hax.Tuple0 := do
    (pure sorry)
  from_slice_i128 (Self) (src : (RustSlice i128)) :RustM
    rust_primitives.hax.Tuple0 := do
    (pure sorry)
  from_slice_f32 (Self) : ((RustSlice f32) -> RustM (RustSlice f32))
  from_slice_f64 (Self) : ((RustSlice f64) -> RustM (RustSlice f64))

attribute [instance_reducible, instance] ByteOrder.trait_constr_ByteOrder_i0

attribute [instance_reducible, instance] ByteOrder.trait_constr_ByteOrder_i1

attribute [instance_reducible, instance] ByteOrder.trait_constr_ByteOrder_i2

attribute [instance_reducible, instance] ByteOrder.trait_constr_ByteOrder_i3

attribute [instance_reducible, instance] ByteOrder.trait_constr_ByteOrder_i4

attribute [instance_reducible, instance] ByteOrder.trait_constr_ByteOrder_i5

attribute [instance_reducible, instance] ByteOrder.trait_constr_ByteOrder_i6

attribute [instance_reducible, instance] ByteOrder.trait_constr_ByteOrder_i7

attribute [instance_reducible, instance] ByteOrder.trait_constr_ByteOrder_i8

attribute [instance_reducible, instance] ByteOrder.trait_constr_ByteOrder_i9

end byteorder


namespace byteorder.io

--  Extends [`Write`] with methods for writing numbers. (For `std::io`.)
-- 
--  Most of the methods defined here have an unconstrained type parameter that
--  must be explicitly instantiated. Typically, it is instantiated with either
--  the [`BigEndian`] or [`LittleEndian`] types defined in this crate.
-- 
--  # Examples
-- 
--  Write unsigned 16 bit big-endian integers to a [`Write`]:
-- 
--  ```rust
--  use byteorder::{BigEndian, WriteBytesExt};
-- 
--  let mut wtr = vec![];
--  wtr.write_u16::<BigEndian>(517).unwrap();
--  wtr.write_u16::<BigEndian>(768).unwrap();
--  assert_eq!(wtr, vec![2, 5, 3, 0]);
--  ```
-- 
--  [`BigEndian`]: enum.BigEndian.html
--  [`LittleEndian`]: enum.LittleEndian.html
--  [`Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
class WriteBytesExt.AssociatedTypes (Self : Type) where
  [trait_constr_WriteBytesExt_i0 : std.io.Write.AssociatedTypes Self]

attribute [instance_reducible, instance]
  WriteBytesExt.AssociatedTypes.trait_constr_WriteBytesExt_i0

class WriteBytesExt (Self : Type)
  [associatedTypes : outParam (WriteBytesExt.AssociatedTypes (Self : Type))]
  where
  [trait_constr_WriteBytesExt_i0 : std.io.Write Self]
  write_u8 (Self) (self : Self) (n : u8) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all
        Self self (← (rust_primitives.unsize (RustArray.ofVec #v[n]))));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_i8 (Self) (self : Self) (n : i8) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all
        Self
        self
        (← (rust_primitives.unsize
          (RustArray.ofVec #v[(← (rust_primitives.hax.cast_op
                                  n :
                                  RustM u8))]))));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_u16 (Self)
    (T : Type)
    [trait_constr_write_u16_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_u16_i1 : byteorder.ByteOrder T ] (self : Self) (n : u16)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 2) ←
      (rust_primitives.hax.repeat (0 : u8) (2 : usize));
    let buf : (RustArray u8 2) ← (byteorder.ByteOrder.write_u16 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_i16 (Self)
    (T : Type)
    [trait_constr_write_i16_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_i16_i1 : byteorder.ByteOrder T ] (self : Self) (n : i16)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 2) ←
      (rust_primitives.hax.repeat (0 : u8) (2 : usize));
    let buf : (RustArray u8 2) ← (byteorder.ByteOrder.write_i16 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_u24 (Self)
    (T : Type)
    [trait_constr_write_u24_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_u24_i1 : byteorder.ByteOrder T ] (self : Self) (n : u32)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 3) ←
      (rust_primitives.hax.repeat (0 : u8) (3 : usize));
    let buf : (RustArray u8 3) ← (byteorder.ByteOrder.write_u24 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_i24 (Self)
    (T : Type)
    [trait_constr_write_i24_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_i24_i1 : byteorder.ByteOrder T ] (self : Self) (n : i32)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 3) ←
      (rust_primitives.hax.repeat (0 : u8) (3 : usize));
    let buf : (RustArray u8 3) ← (byteorder.ByteOrder.write_i24 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_u32 (Self)
    (T : Type)
    [trait_constr_write_u32_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_u32_i1 : byteorder.ByteOrder T ] (self : Self) (n : u32)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 4) ←
      (rust_primitives.hax.repeat (0 : u8) (4 : usize));
    let buf : (RustArray u8 4) ← (byteorder.ByteOrder.write_u32 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_i32 (Self)
    (T : Type)
    [trait_constr_write_i32_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_i32_i1 : byteorder.ByteOrder T ] (self : Self) (n : i32)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 4) ←
      (rust_primitives.hax.repeat (0 : u8) (4 : usize));
    let buf : (RustArray u8 4) ← (byteorder.ByteOrder.write_i32 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_u48 (Self)
    (T : Type)
    [trait_constr_write_u48_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_u48_i1 : byteorder.ByteOrder T ] (self : Self) (n : u64)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 6) ←
      (rust_primitives.hax.repeat (0 : u8) (6 : usize));
    let buf : (RustArray u8 6) ← (byteorder.ByteOrder.write_u48 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_i48 (Self)
    (T : Type)
    [trait_constr_write_i48_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_i48_i1 : byteorder.ByteOrder T ] (self : Self) (n : i64)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 6) ←
      (rust_primitives.hax.repeat (0 : u8) (6 : usize));
    let buf : (RustArray u8 6) ← (byteorder.ByteOrder.write_i48 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_u64 (Self)
    (T : Type)
    [trait_constr_write_u64_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_u64_i1 : byteorder.ByteOrder T ] (self : Self) (n : u64)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let buf : (RustArray u8 8) ← (byteorder.ByteOrder.write_u64 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_i64 (Self)
    (T : Type)
    [trait_constr_write_i64_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_i64_i1 : byteorder.ByteOrder T ] (self : Self) (n : i64)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let buf : (RustArray u8 8) ← (byteorder.ByteOrder.write_i64 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_u128 (Self)
    (T : Type)
    [trait_constr_write_u128_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_u128_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (n : u128) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 16) ←
      (rust_primitives.hax.repeat (0 : u8) (16 : usize));
    let buf : (RustArray u8 16) ← (byteorder.ByteOrder.write_u128 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_i128 (Self)
    (T : Type)
    [trait_constr_write_i128_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_i128_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (n : i128) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 16) ←
      (rust_primitives.hax.repeat (0 : u8) (16 : usize));
    let buf : (RustArray u8 16) ← (byteorder.ByteOrder.write_i128 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_uint (Self)
    (T : Type)
    [trait_constr_write_uint_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_uint_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (n : u64)
    (nbytes : usize) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let buf : (RustArray u8 8) ←
      (byteorder.ByteOrder.write_uint T buf n nbytes);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all
        Self
        self
        (← buf[
          (core_models.ops.range.Range.mk
            (start := (0 : usize))
            (_end := nbytes))
          ]_?));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_int (Self)
    (T : Type)
    [trait_constr_write_int_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_int_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (n : i64)
    (nbytes : usize) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let buf : (RustArray u8 8) ← (byteorder.ByteOrder.write_int T buf n nbytes);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all
        Self
        self
        (← buf[
          (core_models.ops.range.Range.mk
            (start := (0 : usize))
            (_end := nbytes))
          ]_?));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_uint128 (Self)
    (T : Type)
    [trait_constr_write_uint128_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_uint128_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (n : u128)
    (nbytes : usize) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 16) ←
      (rust_primitives.hax.repeat (0 : u8) (16 : usize));
    let buf : (RustArray u8 16) ←
      (byteorder.ByteOrder.write_uint128 T buf n nbytes);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all
        Self
        self
        (← buf[
          (core_models.ops.range.Range.mk
            (start := (0 : usize))
            (_end := nbytes))
          ]_?));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_int128 (Self)
    (T : Type)
    [trait_constr_write_int128_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_int128_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (n : i128)
    (nbytes : usize) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 16) ←
      (rust_primitives.hax.repeat (0 : u8) (16 : usize));
    let buf : (RustArray u8 16) ←
      (byteorder.ByteOrder.write_int128 T buf n nbytes);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all
        Self
        self
        (← buf[
          (core_models.ops.range.Range.mk
            (start := (0 : usize))
            (_end := nbytes))
          ]_?));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_f32 (Self)
    (T : Type)
    [trait_constr_write_f32_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_f32_i1 : byteorder.ByteOrder T ] (self : Self) (n : f32)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 4) ←
      (rust_primitives.hax.repeat (0 : u8) (4 : usize));
    let buf : (RustArray u8 4) ← (byteorder.ByteOrder.write_f32 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
  write_f64 (Self)
    (T : Type)
    [trait_constr_write_f64_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_write_f64_i1 : byteorder.ByteOrder T ] (self : Self) (n : f64)
    :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let buf : (RustArray u8 8) ← (byteorder.ByteOrder.write_f64 T buf n);
    let ⟨tmp0, out⟩ ←
      (std.io.Write.write_all Self self (← (rust_primitives.unsize buf)));
    let self : Self := tmp0;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

attribute [instance_reducible, instance]
  WriteBytesExt.trait_constr_WriteBytesExt_i0

--  All types that implement `Write` get methods defined in `WriteBytesExt`
--  for free.
@[reducible] instance Impl_1.AssociatedTypes
  (W : Type)
  [trait_constr_Impl_1_associated_type_i0 : std.io.Write.AssociatedTypes W]
  [trait_constr_Impl_1_i0 : std.io.Write W ] :
  WriteBytesExt.AssociatedTypes W
  where

instance Impl_1
  (W : Type)
  [trait_constr_Impl_1_associated_type_i0 : std.io.Write.AssociatedTypes W]
  [trait_constr_Impl_1_i0 : std.io.Write W ] :
  WriteBytesExt W
  where

end byteorder.io


namespace byteorder

@[reducible] instance Impl_2.AssociatedTypes :
  ByteOrder.AssociatedTypes BigEndian
  where

instance Impl_2 : ByteOrder BigEndian where
  read_u16 := fun (buf : (RustSlice u8)) => do
    (core_models.num.Impl_7.from_be_bytes
      (← (core_models.result.Impl.unwrap
        (RustArray u8 2)
        core_models.array.TryFromSliceError
        (← (core_models.convert.TryInto.try_into
          (RustSlice u8)
          (RustArray u8 2)
          (← buf[
            (core_models.ops.range.RangeTo.mk (_end := (2 : usize)))
            ]_?))))))
  read_u32 := fun (buf : (RustSlice u8)) => do
    (core_models.num.Impl_8.from_be_bytes
      (← (core_models.result.Impl.unwrap
        (RustArray u8 4)
        core_models.array.TryFromSliceError
        (← (core_models.convert.TryInto.try_into
          (RustSlice u8)
          (RustArray u8 4)
          (← buf[
            (core_models.ops.range.RangeTo.mk (_end := (4 : usize)))
            ]_?))))))
  read_u64 := fun (buf : (RustSlice u8)) => do
    (core_models.num.Impl_9.from_be_bytes
      (← (core_models.result.Impl.unwrap
        (RustArray u8 8)
        core_models.array.TryFromSliceError
        (← (core_models.convert.TryInto.try_into
          (RustSlice u8)
          (RustArray u8 8)
          (← buf[
            (core_models.ops.range.RangeTo.mk (_end := (8 : usize)))
            ]_?))))))
  read_u128 := fun (buf : (RustSlice u8)) => do
    (core_models.num.Impl_10.from_be_bytes
      (← (core_models.result.Impl.unwrap
        (RustArray u8 16)
        core_models.array.TryFromSliceError
        (← (core_models.convert.TryInto.try_into
          (RustSlice u8)
          (RustArray u8 16)
          (← buf[
            (core_models.ops.range.RangeTo.mk (_end := (16 : usize)))
            ]_?))))))
  read_uint := fun (buf : (RustSlice u8)) (nbytes : usize) => do
    let out : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let _ ←
      (hax_lib.assert
        (← ((← ((← ((1 : usize) <=? nbytes))
            &&? (← (nbytes
              <=? (← (core_models.slice.Impl.len u8
                (← (rust_primitives.unsize out))))))))
          &&? (← (nbytes <=? (← (core_models.slice.Impl.len u8 buf)))))));
    let start : usize ←
      ((← (core_models.slice.Impl.len u8 (← (rust_primitives.unsize out))))
        -? nbytes);
    let out : (RustArray u8 8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_from
        out
        (core_models.ops.range.RangeFrom.mk (start := start))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← out[(core_models.ops.range.RangeFrom.mk (start := start))]_?)
          (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?))));
    (core_models.num.Impl_9.from_be_bytes out)
  read_uint128 := fun (buf : (RustSlice u8)) (nbytes : usize) => do
    let out : (RustArray u8 16) ←
      (rust_primitives.hax.repeat (0 : u8) (16 : usize));
    let _ ←
      (hax_lib.assert
        (← ((← ((← ((1 : usize) <=? nbytes))
            &&? (← (nbytes
              <=? (← (core_models.slice.Impl.len u8
                (← (rust_primitives.unsize out))))))))
          &&? (← (nbytes <=? (← (core_models.slice.Impl.len u8 buf)))))));
    let start : usize ←
      ((← (core_models.slice.Impl.len u8 (← (rust_primitives.unsize out))))
        -? nbytes);
    let out : (RustArray u8 16) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_from
        out
        (core_models.ops.range.RangeFrom.mk (start := start))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← out[(core_models.ops.range.RangeFrom.mk (start := start))]_?)
          (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?))));
    (core_models.num.Impl_10.from_be_bytes out)
  write_u16 := fun (buf : (RustSlice u8)) (n : u16) => do
    let buf : (RustSlice u8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := (2 : usize)))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← buf[(core_models.ops.range.RangeTo.mk (_end := (2 : usize)))]_?)
          (← (rust_primitives.unsize
            (← (core_models.num.Impl_7.to_be_bytes n)))))));
    (pure buf)
  write_u32 := fun (buf : (RustSlice u8)) (n : u32) => do
    let buf : (RustSlice u8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := (4 : usize)))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← buf[(core_models.ops.range.RangeTo.mk (_end := (4 : usize)))]_?)
          (← (rust_primitives.unsize
            (← (core_models.num.Impl_8.to_be_bytes n)))))));
    (pure buf)
  write_u64 := fun (buf : (RustSlice u8)) (n : u64) => do
    let buf : (RustSlice u8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := (8 : usize)))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← buf[(core_models.ops.range.RangeTo.mk (_end := (8 : usize)))]_?)
          (← (rust_primitives.unsize
            (← (core_models.num.Impl_9.to_be_bytes n)))))));
    (pure buf)
  write_u128 := fun (buf : (RustSlice u8)) (n : u128) => do
    let buf : (RustSlice u8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := (16 : usize)))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← buf[(core_models.ops.range.RangeTo.mk (_end := (16 : usize)))]_?)
          (← (rust_primitives.unsize
            (← (core_models.num.Impl_10.to_be_bytes n)))))));
    (pure buf)
  write_uint := fun (buf : (RustSlice u8)) (n : u64) (nbytes : usize) => do
    let _ ←
      (hax_lib.assert
        (← ((← ((← (pack_size n)) <=? nbytes))
          &&? (← (nbytes <=? (8 : usize))))));
    let _ ←
      (hax_lib.assert (← (nbytes <=? (← (core_models.slice.Impl.len u8 buf)))));
    let bytes : (RustArray u8 8) := sorry;
    let _ := sorry;
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure buf)
  write_uint128 := fun (buf : (RustSlice u8)) (n : u128) (nbytes : usize) => do
    let _ ←
      (hax_lib.assert
        (← ((← ((← (pack_size128 n)) <=? nbytes))
          &&? (← (nbytes <=? (16 : usize))))));
    let _ ←
      (hax_lib.assert (← (nbytes <=? (← (core_models.slice.Impl.len u8 buf)))));
    let bytes : (RustArray u8 16) := sorry;
    let _ := sorry;
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure buf)
  read_u16_into := fun (src : (RustSlice u8)) (dst : (RustSlice u16)) => do
    let src : (RustSlice u8) := src;
    let _ := sorry;
    (pure dst)
  read_u32_into := fun (src : (RustSlice u8)) (dst : (RustSlice u32)) => do
    let src : (RustSlice u8) := src;
    let _ := sorry;
    (pure dst)
  read_u64_into := fun (src : (RustSlice u8)) (dst : (RustSlice u64)) => do
    let src : (RustSlice u8) := src;
    let _ := sorry;
    (pure dst)
  read_u128_into := fun (src : (RustSlice u8)) (dst : (RustSlice u128)) => do
    let src : (RustSlice u8) := src;
    let _ := sorry;
    (pure dst)
  write_u16_into := fun (src : (RustSlice u16)) (dst : (RustSlice u8)) => do
    let src : (RustSlice u16) := src;
    let _ := sorry;
    (pure dst)
  write_u32_into := fun (src : (RustSlice u32)) (dst : (RustSlice u8)) => do
    let src : (RustSlice u32) := src;
    let _ := sorry;
    (pure dst)
  write_u64_into := fun (src : (RustSlice u64)) (dst : (RustSlice u8)) => do
    let src : (RustSlice u64) := src;
    let _ := sorry;
    (pure dst)
  write_u128_into := fun (src : (RustSlice u128)) (dst : (RustSlice u8)) => do
    let src : (RustSlice u128) := src;
    let _ := sorry;
    (pure dst)
  from_slice_u16 := fun (numbers : (RustSlice u16)) => do
    let _ ←
      if true then do (pure sorry) else do (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)
  from_slice_u32 := fun (numbers : (RustSlice u32)) => do
    let _ ←
      if true then do (pure sorry) else do (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)
  from_slice_u64 := fun (numbers : (RustSlice u64)) => do
    let _ ←
      if true then do (pure sorry) else do (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)
  from_slice_u128 := fun (numbers : (RustSlice u128)) => do
    let _ ←
      if true then do (pure sorry) else do (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)
  from_slice_f32 := fun (numbers : (RustSlice f32)) => do
    let _ ←
      if true then do (pure sorry) else do (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)
  from_slice_f64 := fun (numbers : (RustSlice f64)) => do
    let _ ←
      if true then do (pure sorry) else do (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)

@[reducible] instance Impl_3.AssociatedTypes :
  ByteOrder.AssociatedTypes LittleEndian
  where

instance Impl_3 : ByteOrder LittleEndian where
  read_u16 := fun (buf : (RustSlice u8)) => do
    (core_models.num.Impl_7.from_le_bytes
      (← (core_models.result.Impl.unwrap
        (RustArray u8 2)
        core_models.array.TryFromSliceError
        (← (core_models.convert.TryInto.try_into
          (RustSlice u8)
          (RustArray u8 2)
          (← buf[
            (core_models.ops.range.RangeTo.mk (_end := (2 : usize)))
            ]_?))))))
  read_u32 := fun (buf : (RustSlice u8)) => do
    (core_models.num.Impl_8.from_le_bytes
      (← (core_models.result.Impl.unwrap
        (RustArray u8 4)
        core_models.array.TryFromSliceError
        (← (core_models.convert.TryInto.try_into
          (RustSlice u8)
          (RustArray u8 4)
          (← buf[
            (core_models.ops.range.RangeTo.mk (_end := (4 : usize)))
            ]_?))))))
  read_u64 := fun (buf : (RustSlice u8)) => do
    (core_models.num.Impl_9.from_le_bytes
      (← (core_models.result.Impl.unwrap
        (RustArray u8 8)
        core_models.array.TryFromSliceError
        (← (core_models.convert.TryInto.try_into
          (RustSlice u8)
          (RustArray u8 8)
          (← buf[
            (core_models.ops.range.RangeTo.mk (_end := (8 : usize)))
            ]_?))))))
  read_u128 := fun (buf : (RustSlice u8)) => do
    (core_models.num.Impl_10.from_le_bytes
      (← (core_models.result.Impl.unwrap
        (RustArray u8 16)
        core_models.array.TryFromSliceError
        (← (core_models.convert.TryInto.try_into
          (RustSlice u8)
          (RustArray u8 16)
          (← buf[
            (core_models.ops.range.RangeTo.mk (_end := (16 : usize)))
            ]_?))))))
  read_uint := fun (buf : (RustSlice u8)) (nbytes : usize) => do
    let out : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let _ ←
      (hax_lib.assert
        (← ((← ((← ((1 : usize) <=? nbytes))
            &&? (← (nbytes
              <=? (← (core_models.slice.Impl.len u8
                (← (rust_primitives.unsize out))))))))
          &&? (← (nbytes <=? (← (core_models.slice.Impl.len u8 buf)))))));
    let out : (RustArray u8 8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        out
        (core_models.ops.range.RangeTo.mk (_end := nbytes))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← out[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?)
          (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?))));
    (core_models.num.Impl_9.from_le_bytes out)
  read_uint128 := fun (buf : (RustSlice u8)) (nbytes : usize) => do
    let out : (RustArray u8 16) ←
      (rust_primitives.hax.repeat (0 : u8) (16 : usize));
    let _ ←
      (hax_lib.assert
        (← ((← ((← ((1 : usize) <=? nbytes))
            &&? (← (nbytes
              <=? (← (core_models.slice.Impl.len u8
                (← (rust_primitives.unsize out))))))))
          &&? (← (nbytes <=? (← (core_models.slice.Impl.len u8 buf)))))));
    let out : (RustArray u8 16) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        out
        (core_models.ops.range.RangeTo.mk (_end := nbytes))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← out[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?)
          (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?))));
    (core_models.num.Impl_10.from_le_bytes out)
  write_u16 := fun (buf : (RustSlice u8)) (n : u16) => do
    let buf : (RustSlice u8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := (2 : usize)))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← buf[(core_models.ops.range.RangeTo.mk (_end := (2 : usize)))]_?)
          (← (rust_primitives.unsize
            (← (core_models.num.Impl_7.to_le_bytes n)))))));
    (pure buf)
  write_u32 := fun (buf : (RustSlice u8)) (n : u32) => do
    let buf : (RustSlice u8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := (4 : usize)))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← buf[(core_models.ops.range.RangeTo.mk (_end := (4 : usize)))]_?)
          (← (rust_primitives.unsize
            (← (core_models.num.Impl_8.to_le_bytes n)))))));
    (pure buf)
  write_u64 := fun (buf : (RustSlice u8)) (n : u64) => do
    let buf : (RustSlice u8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := (8 : usize)))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← buf[(core_models.ops.range.RangeTo.mk (_end := (8 : usize)))]_?)
          (← (rust_primitives.unsize
            (← (core_models.num.Impl_9.to_le_bytes n)))))));
    (pure buf)
  write_u128 := fun (buf : (RustSlice u8)) (n : u128) => do
    let buf : (RustSlice u8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := (16 : usize)))
        (← (core_models.slice.Impl.copy_from_slice u8
          (← buf[(core_models.ops.range.RangeTo.mk (_end := (16 : usize)))]_?)
          (← (rust_primitives.unsize
            (← (core_models.num.Impl_10.to_le_bytes n)))))));
    (pure buf)
  write_uint := fun (buf : (RustSlice u8)) (n : u64) (nbytes : usize) => do
    let _ ←
      (hax_lib.assert
        (← ((← ((← (pack_size n)) <=? nbytes))
          &&? (← (nbytes <=? (8 : usize))))));
    let _ ←
      (hax_lib.assert (← (nbytes <=? (← (core_models.slice.Impl.len u8 buf)))));
    let bytes : (RustArray u8 8) := sorry;
    let _ := sorry;
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure buf)
  write_uint128 := fun (buf : (RustSlice u8)) (n : u128) (nbytes : usize) => do
    let _ ←
      (hax_lib.assert
        (← ((← ((← (pack_size128 n)) <=? nbytes))
          &&? (← (nbytes <=? (16 : usize))))));
    let _ ←
      (hax_lib.assert (← (nbytes <=? (← (core_models.slice.Impl.len u8 buf)))));
    let bytes : (RustArray u8 16) := sorry;
    let _ := sorry;
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure buf)
  read_u16_into := fun (src : (RustSlice u8)) (dst : (RustSlice u16)) => do
    let src : (RustSlice u8) := src;
    let _ := sorry;
    (pure dst)
  read_u32_into := fun (src : (RustSlice u8)) (dst : (RustSlice u32)) => do
    let src : (RustSlice u8) := src;
    let _ := sorry;
    (pure dst)
  read_u64_into := fun (src : (RustSlice u8)) (dst : (RustSlice u64)) => do
    let src : (RustSlice u8) := src;
    let _ := sorry;
    (pure dst)
  read_u128_into := fun (src : (RustSlice u8)) (dst : (RustSlice u128)) => do
    let src : (RustSlice u8) := src;
    let _ := sorry;
    (pure dst)
  write_u16_into := fun (src : (RustSlice u16)) (dst : (RustSlice u8)) => do
    let src : (RustSlice u16) := src;
    let _ := sorry;
    (pure dst)
  write_u32_into := fun (src : (RustSlice u32)) (dst : (RustSlice u8)) => do
    let src : (RustSlice u32) := src;
    let _ := sorry;
    (pure dst)
  write_u64_into := fun (src : (RustSlice u64)) (dst : (RustSlice u8)) => do
    let src : (RustSlice u64) := src;
    let _ := sorry;
    (pure dst)
  write_u128_into := fun (src : (RustSlice u128)) (dst : (RustSlice u8)) => do
    let src : (RustSlice u128) := src;
    let _ := sorry;
    (pure dst)
  from_slice_u16 := fun (numbers : (RustSlice u16)) => do
    let _ ←
      if false then do
        (pure sorry)
      else do
        (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)
  from_slice_u32 := fun (numbers : (RustSlice u32)) => do
    let _ ←
      if false then do
        (pure sorry)
      else do
        (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)
  from_slice_u64 := fun (numbers : (RustSlice u64)) => do
    let _ ←
      if false then do
        (pure sorry)
      else do
        (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)
  from_slice_u128 := fun (numbers : (RustSlice u128)) => do
    let _ ←
      if false then do
        (pure sorry)
      else do
        (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)
  from_slice_f32 := fun (numbers : (RustSlice f32)) => do
    let _ ←
      if false then do
        (pure sorry)
      else do
        (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)
  from_slice_f64 := fun (numbers : (RustSlice f64)) => do
    let _ ←
      if false then do
        (pure sorry)
      else do
        (pure rust_primitives.hax.Tuple0.mk);
    (pure numbers)

end byteorder


namespace byteorder.io

--  Extends [`Read`] with methods for reading numbers. (For `std::io`.)
-- 
--  Most of the methods defined here have an unconstrained type parameter that
--  must be explicitly instantiated. Typically, it is instantiated with either
--  the [`BigEndian`] or [`LittleEndian`] types defined in this crate.
-- 
--  # Examples
-- 
--  Read unsigned 16 bit big-endian integers from a [`Read`]:
-- 
--  ```rust
--  use std::io::Cursor;
--  use byteorder::{BigEndian, ReadBytesExt};
-- 
--  let mut rdr = Cursor::new(vec![2, 5, 3, 0]);
--  assert_eq!(517, rdr.read_u16::<BigEndian>().unwrap());
--  assert_eq!(768, rdr.read_u16::<BigEndian>().unwrap());
--  ```
-- 
--  [`BigEndian`]: enum.BigEndian.html
--  [`LittleEndian`]: enum.LittleEndian.html
--  [`Read`]: https://doc.rust-lang.org/std/io/trait.Read.html
class ReadBytesExt.AssociatedTypes (Self : Type) where
  [trait_constr_ReadBytesExt_i0 : std.io.Read.AssociatedTypes Self]

attribute [instance_reducible, instance]
  ReadBytesExt.AssociatedTypes.trait_constr_ReadBytesExt_i0

class ReadBytesExt (Self : Type)
  [associatedTypes : outParam (ReadBytesExt.AssociatedTypes (Self : Type))]
  where
  [trait_constr_ReadBytesExt_i0 : std.io.Read Self]
  read_u8 (Self) (self : Self) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result u8 std.io.error.Error)) := do
    let buf : (RustArray u8 1) ←
      (rust_primitives.hax.repeat (0 : u8) (1 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 1) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result u8 std.io.error.Error) :=
          (core_models.result.Result.Ok (← buf[(0 : usize)]_?));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_i8 (Self) (self : Self) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result i8 std.io.error.Error)) := do
    let buf : (RustArray u8 1) ←
      (rust_primitives.hax.repeat (0 : u8) (1 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 1) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result i8 std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (rust_primitives.hax.cast_op
              (← buf[(0 : usize)]_?) :
              RustM i8)));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_u16 (Self)
    (T : Type)
    [trait_constr_read_u16_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_u16_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result u16 std.io.error.Error)) := do
    let buf : (RustArray u8 2) ←
      (rust_primitives.hax.repeat (0 : u8) (2 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 2) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            u16
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_u16
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_i16 (Self)
    (T : Type)
    [trait_constr_read_i16_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_i16_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result i16 std.io.error.Error)) := do
    let buf : (RustArray u8 2) ←
      (rust_primitives.hax.repeat (0 : u8) (2 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 2) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            i16
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_i16
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_u24 (Self)
    (T : Type)
    [trait_constr_read_u24_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_u24_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result u32 std.io.error.Error)) := do
    let buf : (RustArray u8 3) ←
      (rust_primitives.hax.repeat (0 : u8) (3 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 3) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            u32
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_u24
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_i24 (Self)
    (T : Type)
    [trait_constr_read_i24_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_i24_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result i32 std.io.error.Error)) := do
    let buf : (RustArray u8 3) ←
      (rust_primitives.hax.repeat (0 : u8) (3 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 3) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            i32
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_i24
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_u32 (Self)
    (T : Type)
    [trait_constr_read_u32_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_u32_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result u32 std.io.error.Error)) := do
    let buf : (RustArray u8 4) ←
      (rust_primitives.hax.repeat (0 : u8) (4 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 4) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            u32
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_u32
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_i32 (Self)
    (T : Type)
    [trait_constr_read_i32_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_i32_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result i32 std.io.error.Error)) := do
    let buf : (RustArray u8 4) ←
      (rust_primitives.hax.repeat (0 : u8) (4 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 4) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            i32
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_i32
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_u48 (Self)
    (T : Type)
    [trait_constr_read_u48_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_u48_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result u64 std.io.error.Error)) := do
    let buf : (RustArray u8 6) ←
      (rust_primitives.hax.repeat (0 : u8) (6 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 6) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            u64
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_u48
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_i48 (Self)
    (T : Type)
    [trait_constr_read_i48_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_i48_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result i64 std.io.error.Error)) := do
    let buf : (RustArray u8 6) ←
      (rust_primitives.hax.repeat (0 : u8) (6 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 6) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            i64
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_i48
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_u64 (Self)
    (T : Type)
    [trait_constr_read_u64_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_u64_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result u64 std.io.error.Error)) := do
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 8) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            u64
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_u64
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_i64 (Self)
    (T : Type)
    [trait_constr_read_i64_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_i64_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result i64 std.io.error.Error)) := do
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 8) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            i64
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_i64
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_u128 (Self)
    (T : Type)
    [trait_constr_read_u128_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_u128_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result u128 std.io.error.Error)) := do
    let buf : (RustArray u8 16) ←
      (rust_primitives.hax.repeat (0 : u8) (16 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 16) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            u128
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_u128
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_i128 (Self)
    (T : Type)
    [trait_constr_read_i128_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_i128_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result i128 std.io.error.Error)) := do
    let buf : (RustArray u8 16) ←
      (rust_primitives.hax.repeat (0 : u8) (16 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 16) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            i128
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_i128
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_uint (Self)
    (T : Type)
    [trait_constr_read_uint_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_uint_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (nbytes : usize) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result u64 std.io.error.Error)) := do
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let ⟨tmp0, tmp1, out⟩ ←
      (std.io.Read.read_exact
        Self
        self
        (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?));
    let self : Self := tmp0;
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := nbytes))
        tmp1);
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            u64
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_uint
              T
              (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?)
              nbytes)));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_int (Self)
    (T : Type)
    [trait_constr_read_int_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_int_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (nbytes : usize) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result i64 std.io.error.Error)) := do
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let ⟨tmp0, tmp1, out⟩ ←
      (std.io.Read.read_exact
        Self
        self
        (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?));
    let self : Self := tmp0;
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := nbytes))
        tmp1);
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            i64
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_int
              T
              (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?)
              nbytes)));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_uint128 (Self)
    (T : Type)
    [trait_constr_read_uint128_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_uint128_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (nbytes : usize) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result u128 std.io.error.Error)) := do
    let buf : (RustArray u8 16) ←
      (rust_primitives.hax.repeat (0 : u8) (16 : usize));
    let ⟨tmp0, tmp1, out⟩ ←
      (std.io.Read.read_exact
        Self
        self
        (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?));
    let self : Self := tmp0;
    let buf : (RustArray u8 16) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := nbytes))
        tmp1);
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            u128
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_uint128
              T
              (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?)
              nbytes)));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_int128 (Self)
    (T : Type)
    [trait_constr_read_int128_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_int128_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (nbytes : usize) :RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result i128 std.io.error.Error)) := do
    let buf : (RustArray u8 16) ←
      (rust_primitives.hax.repeat (0 : u8) (16 : usize));
    let ⟨tmp0, tmp1, out⟩ ←
      (std.io.Read.read_exact
        Self
        self
        (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?));
    let self : Self := tmp0;
    let buf : (RustArray u8 16) ←
      (rust_primitives.hax.monomorphized_update_at.update_at_range_to
        buf
        (core_models.ops.range.RangeTo.mk (_end := nbytes))
        tmp1);
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            i128
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_int128
              T
              (← buf[(core_models.ops.range.RangeTo.mk (_end := nbytes))]_?)
              nbytes)));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_f32 (Self)
    (T : Type)
    [trait_constr_read_f32_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_f32_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result f32 std.io.error.Error)) := do
    let buf : (RustArray u8 4) ←
      (rust_primitives.hax.repeat (0 : u8) (4 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 4) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            f32
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_f32
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_f64 (Self)
    (T : Type)
    [trait_constr_read_f64_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_f64_i1 : byteorder.ByteOrder T ] (self : Self) :RustM
    (rust_primitives.hax.Tuple2
      Self
      (core_models.result.Result f64 std.io.error.Error)) := do
    let buf : (RustArray u8 8) ←
      (rust_primitives.hax.repeat (0 : u8) (8 : usize));
    let ⟨tmp0, tmp1, out⟩ ← (std.io.Read.read_exact Self self buf);
    let self : Self := tmp0;
    let buf : (RustArray u8 8) := tmp1;
    match out with
      | (core_models.result.Result.Ok  _) => do
        let
          hax_temp_output : (core_models.result.Result
            f64
            std.io.error.Error) :=
          (core_models.result.Result.Ok
            (← (byteorder.ByteOrder.read_f64
              T (← (rust_primitives.unsize buf)))));
        (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))
      | (core_models.result.Result.Err  err) => do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.result.Result.Err err)))
  read_u16_into (Self)
    (T : Type)
    [trait_constr_read_u16_into_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_u16_into_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice u16)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice u16)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let _ := sorry;
    let dst : (RustSlice u16) ← (byteorder.ByteOrder.from_slice_u16 T dst);
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))
  read_u32_into (Self)
    (T : Type)
    [trait_constr_read_u32_into_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_u32_into_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice u32)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice u32)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let _ := sorry;
    let dst : (RustSlice u32) ← (byteorder.ByteOrder.from_slice_u32 T dst);
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))
  read_u64_into (Self)
    (T : Type)
    [trait_constr_read_u64_into_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_u64_into_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice u64)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice u64)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let _ := sorry;
    let dst : (RustSlice u64) ← (byteorder.ByteOrder.from_slice_u64 T dst);
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))
  read_u128_into (Self)
    (T : Type)
    [trait_constr_read_u128_into_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_u128_into_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice u128)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice u128)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let _ := sorry;
    let dst : (RustSlice u128) ← (byteorder.ByteOrder.from_slice_u128 T dst);
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))
  read_i8_into (Self) (self : Self) (dst : (RustSlice i8)) :RustM
    (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error) :=
    do
    (pure sorry)
  read_i16_into (Self)
    (T : Type)
    [trait_constr_read_i16_into_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_i16_into_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice i16)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice i16)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let _ := sorry;
    let dst : (RustSlice i16) ← (byteorder.ByteOrder.from_slice_i16 T dst);
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))
  read_i32_into (Self)
    (T : Type)
    [trait_constr_read_i32_into_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_i32_into_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice i32)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice i32)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let _ := sorry;
    let dst : (RustSlice i32) ← (byteorder.ByteOrder.from_slice_i32 T dst);
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))
  read_i64_into (Self)
    (T : Type)
    [trait_constr_read_i64_into_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_i64_into_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice i64)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice i64)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let _ := sorry;
    let dst : (RustSlice i64) ← (byteorder.ByteOrder.from_slice_i64 T dst);
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))
  read_i128_into (Self)
    (T : Type)
    [trait_constr_read_i128_into_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_i128_into_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice i128)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice i128)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let _ := sorry;
    let dst : (RustSlice i128) ← (byteorder.ByteOrder.from_slice_i128 T dst);
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))
  read_f32_into (Self)
    (T : Type)
    [trait_constr_read_f32_into_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_f32_into_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice f32)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice f32)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let _ := sorry;
    let dst : (RustSlice f32) ← (byteorder.ByteOrder.from_slice_f32 T dst);
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))
  read_f32_into_unchecked (Self)
    (T : Type)
    [trait_constr_read_f32_into_unchecked_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_f32_into_unchecked_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice f32)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice f32)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let ⟨tmp0, tmp1, out⟩ ← (ReadBytesExt.read_f32_into Self T self dst);
    let self : Self := tmp0;
    let dst : (RustSlice f32) := tmp1;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))
  read_f64_into (Self)
    (T : Type)
    [trait_constr_read_f64_into_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_f64_into_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice f64)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice f64)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let _ := sorry;
    let dst : (RustSlice f64) ← (byteorder.ByteOrder.from_slice_f64 T dst);
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))
  read_f64_into_unchecked (Self)
    (T : Type)
    [trait_constr_read_f64_into_unchecked_associated_type_i1 :
      byteorder.ByteOrder.AssociatedTypes
      T]
    [trait_constr_read_f64_into_unchecked_i1 : byteorder.ByteOrder T ]
    (self : Self)
    (dst : (RustSlice f64)) :RustM (rust_primitives.hax.Tuple3
      Self
      (RustSlice f64)
      (core_models.result.Result rust_primitives.hax.Tuple0 std.io.error.Error))
    := do
    let ⟨tmp0, tmp1, out⟩ ← (ReadBytesExt.read_f64_into Self T self dst);
    let self : Self := tmp0;
    let dst : (RustSlice f64) := tmp1;
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        std.io.error.Error) :=
      out;
    (pure (rust_primitives.hax.Tuple3.mk self dst hax_temp_output))

attribute [instance_reducible, instance]
  ReadBytesExt.trait_constr_ReadBytesExt_i0

--  All types that implement `Read` get methods defined in `ReadBytesExt`
--  for free.
@[reducible] instance Impl.AssociatedTypes
  (R : Type)
  [trait_constr_Impl_associated_type_i0 : std.io.Read.AssociatedTypes R]
  [trait_constr_Impl_i0 : std.io.Read R ] :
  ReadBytesExt.AssociatedTypes R
  where

instance Impl
  (R : Type)
  [trait_constr_Impl_associated_type_i0 : std.io.Read.AssociatedTypes R]
  [trait_constr_Impl_i0 : std.io.Read R ] :
  ReadBytesExt R
  where

end byteorder.io

