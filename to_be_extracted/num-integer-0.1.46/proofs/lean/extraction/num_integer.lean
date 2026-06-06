
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


namespace num_integer.roots

@[spec]
def bits (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM u32 := do
  ((8 : u32)
    *? (← (rust_primitives.hax.cast_op
      (← (core_models.mem.size_of T rust_primitives.hax.Tuple0.mk)) :
      RustM u32)))

@[spec]
def log2
    (T : Type)
    [trait_constr_log2_associated_type_i0 :
      num_traits.int.PrimInt.AssociatedTypes
      T]
    [trait_constr_log2_i0 : num_traits.int.PrimInt T ]
    (x : T) :
    RustM u32 := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← (core_models.cmp.PartialOrd.gt
            T
            T
            x
            (← (num_traits.identities.Zero.zero
              T rust_primitives.hax.Tuple0.mk)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  ((← ((← (bits T rust_primitives.hax.Tuple0.mk)) -? (1 : u32)))
    -? (← (num_traits.int.PrimInt.leading_zeros T x)))

@[spec]
def Impl_6.nth_root.go.guess (x : u8) (n : u32) : RustM u8 := do
  if
  (← ((← ((← (bits u8 rust_primitives.hax.Tuple0.mk)) <=? (32 : u32)))
    ||? (← (x
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u32.MAX :
        RustM u8)))))) then do
    ((1 : u8) <<<? (← ((← ((← ((← (log2 u8 x)) +? n)) -? (1 : u32))) /? n)))
  else do
    (rust_primitives.hax.cast_op
      (← (std.f64.Impl.exp
        (← (core_models.ops.arith.Div.div
          (← (std.f64.Impl.ln (← (rust_primitives.hax.cast_op x : RustM f64))))
          (← (core_models.convert.From._from f64 u32 n)))))) :
      RustM u8)

@[spec]
def Impl_6.sqrt.go.guess (x : u8) : RustM u8 := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.sqrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM u8)

@[spec]
def Impl_6.cbrt.go.guess (x : u8) : RustM u8 := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.cbrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM u8)

@[spec]
def Impl_7.nth_root.go.guess (x : u16) (n : u32) : RustM u16 := do
  if
  (← ((← ((← (bits u16 rust_primitives.hax.Tuple0.mk)) <=? (32 : u32)))
    ||? (← (x
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u32.MAX :
        RustM u16)))))) then do
    ((1 : u16) <<<? (← ((← ((← ((← (log2 u16 x)) +? n)) -? (1 : u32))) /? n)))
  else do
    (rust_primitives.hax.cast_op
      (← (std.f64.Impl.exp
        (← (core_models.ops.arith.Div.div
          (← (std.f64.Impl.ln (← (rust_primitives.hax.cast_op x : RustM f64))))
          (← (core_models.convert.From._from f64 u32 n)))))) :
      RustM u16)

@[spec]
def Impl_7.sqrt.go.guess (x : u16) : RustM u16 := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.sqrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM u16)

@[spec]
def Impl_7.cbrt.go.guess (x : u16) : RustM u16 := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.cbrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM u16)

@[spec]
def Impl_8.nth_root.go.guess (x : u32) (n : u32) : RustM u32 := do
  if
  (← ((← ((← (bits u32 rust_primitives.hax.Tuple0.mk)) <=? (32 : u32)))
    ||? (← (x <=? core_models.legacy_int_modules.u32.MAX)))) then do
    ((1 : u32) <<<? (← ((← ((← ((← (log2 u32 x)) +? n)) -? (1 : u32))) /? n)))
  else do
    (rust_primitives.hax.cast_op
      (← (std.f64.Impl.exp
        (← (core_models.ops.arith.Div.div
          (← (std.f64.Impl.ln (← (rust_primitives.hax.cast_op x : RustM f64))))
          (← (core_models.convert.From._from f64 u32 n)))))) :
      RustM u32)

@[spec]
def Impl_8.sqrt.go.guess (x : u32) : RustM u32 := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.sqrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM u32)

@[spec]
def Impl_8.cbrt.go.guess (x : u32) : RustM u32 := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.cbrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM u32)

@[spec]
def Impl_9.nth_root.go.guess (x : u64) (n : u32) : RustM u64 := do
  if
  (← ((← ((← (bits u64 rust_primitives.hax.Tuple0.mk)) <=? (32 : u32)))
    ||? (← (x
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u32.MAX :
        RustM u64)))))) then do
    ((1 : u64) <<<? (← ((← ((← ((← (log2 u64 x)) +? n)) -? (1 : u32))) /? n)))
  else do
    (rust_primitives.hax.cast_op
      (← (std.f64.Impl.exp
        (← (core_models.ops.arith.Div.div
          (← (std.f64.Impl.ln (← (rust_primitives.hax.cast_op x : RustM f64))))
          (← (core_models.convert.From._from f64 u32 n)))))) :
      RustM u64)

@[spec]
def Impl_9.sqrt.go.guess (x : u64) : RustM u64 := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.sqrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM u64)

@[spec]
def Impl_9.cbrt.go.guess (x : u64) : RustM u64 := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.cbrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM u64)

@[spec]
def Impl_10.nth_root.go.guess (x : u128) (n : u32) : RustM u128 := do
  if
  (← ((← ((← (bits u128 rust_primitives.hax.Tuple0.mk)) <=? (32 : u32)))
    ||? (← (x
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u32.MAX :
        RustM u128)))))) then do
    ((1 : u128) <<<? (← ((← ((← ((← (log2 u128 x)) +? n)) -? (1 : u32))) /? n)))
  else do
    (rust_primitives.hax.cast_op
      (← (std.f64.Impl.exp
        (← (core_models.ops.arith.Div.div
          (← (std.f64.Impl.ln (← (rust_primitives.hax.cast_op x : RustM f64))))
          (← (core_models.convert.From._from f64 u32 n)))))) :
      RustM u128)

@[spec]
def Impl_10.sqrt.go.guess (x : u128) : RustM u128 := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.sqrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM u128)

@[spec]
def Impl_10.cbrt.go.guess (x : u128) : RustM u128 := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.cbrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM u128)

@[spec]
def Impl_11.nth_root.go.guess (x : usize) (n : u32) : RustM usize := do
  if
  (← ((← ((← (bits usize rust_primitives.hax.Tuple0.mk)) <=? (32 : u32)))
    ||? (← (x
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u32.MAX :
        RustM usize)))))) then do
    ((1 : usize)
      <<<? (← ((← ((← ((← (log2 usize x)) +? n)) -? (1 : u32))) /? n)))
  else do
    (rust_primitives.hax.cast_op
      (← (std.f64.Impl.exp
        (← (core_models.ops.arith.Div.div
          (← (std.f64.Impl.ln (← (rust_primitives.hax.cast_op x : RustM f64))))
          (← (core_models.convert.From._from f64 u32 n)))))) :
      RustM usize)

@[spec]
def Impl_11.sqrt.go.guess (x : usize) : RustM usize := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.sqrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM usize)

@[spec]
def Impl_11.cbrt.go.guess (x : usize) : RustM usize := do
  (rust_primitives.hax.cast_op
    (← (std.f64.Impl.cbrt (← (rust_primitives.hax.cast_op x : RustM f64)))) :
    RustM usize)

end num_integer.roots


namespace num_integer

--  Greatest common divisor and Bézout coefficients
-- 
--  ```no_build
--  let e = isize::extended_gcd(a, b);
--  assert_eq!(e.gcd, e.x*a + e.y*b);
--  ```
structure ExtendedGcd (A : Type) where
  gcd : A
  x : A
  y : A

@[instance] opaque Impl_2.AssociatedTypes
  (A : Type)
  [trait_constr_Impl_2_associated_type_i0 :
    core_models.fmt.Debug.AssociatedTypes
    A]
  [trait_constr_Impl_2_i0 : core_models.fmt.Debug A ] :
  core_models.fmt.Debug.AssociatedTypes (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2
  (A : Type)
  [trait_constr_Impl_2_associated_type_i0 :
    core_models.fmt.Debug.AssociatedTypes
    A]
  [trait_constr_Impl_2_i0 : core_models.fmt.Debug A ] :
  core_models.fmt.Debug (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes
  (A : Type)
  [trait_constr_Impl_3_associated_type_i0 :
    core_models.clone.Clone.AssociatedTypes
    A]
  [trait_constr_Impl_3_i0 : core_models.clone.Clone A ] :
  core_models.clone.Clone.AssociatedTypes (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3
  (A : Type)
  [trait_constr_Impl_3_associated_type_i0 :
    core_models.clone.Clone.AssociatedTypes
    A]
  [trait_constr_Impl_3_i0 : core_models.clone.Clone A ] :
  core_models.clone.Clone (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes
  (A : Type)
  [trait_constr_Impl_4_associated_type_i0 :
    core_models.marker.Copy.AssociatedTypes
    A]
  [trait_constr_Impl_4_i0 : core_models.marker.Copy A ] :
  core_models.marker.Copy.AssociatedTypes (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4
  (A : Type)
  [trait_constr_Impl_4_associated_type_i0 :
    core_models.marker.Copy.AssociatedTypes
    A]
  [trait_constr_Impl_4_i0 : core_models.marker.Copy A ] :
  core_models.marker.Copy (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes (A : Type) :
  core_models.marker.StructuralPartialEq.AssociatedTypes (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 (A : Type) :
  core_models.marker.StructuralPartialEq (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6.AssociatedTypes
  (A : Type)
  [trait_constr_Impl_6_associated_type_i0 :
    core_models.cmp.PartialEq.AssociatedTypes
    A
    A]
  [trait_constr_Impl_6_i0 : core_models.cmp.PartialEq A A ] :
  core_models.cmp.PartialEq.AssociatedTypes (ExtendedGcd A) (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6
  (A : Type)
  [trait_constr_Impl_6_associated_type_i0 :
    core_models.cmp.PartialEq.AssociatedTypes
    A
    A]
  [trait_constr_Impl_6_i0 : core_models.cmp.PartialEq A A ] :
  core_models.cmp.PartialEq (ExtendedGcd A) (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7.AssociatedTypes
  (A : Type)
  [trait_constr_Impl_7_associated_type_i0 : core_models.cmp.Eq.AssociatedTypes
    A]
  [trait_constr_Impl_7_i0 : core_models.cmp.Eq A ] :
  core_models.cmp.Eq.AssociatedTypes (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7
  (A : Type)
  [trait_constr_Impl_7_associated_type_i0 : core_models.cmp.Eq.AssociatedTypes
    A]
  [trait_constr_Impl_7_i0 : core_models.cmp.Eq A ] :
  core_models.cmp.Eq (ExtendedGcd A) :=
  by constructor <;> exact Inhabited.default

--  An iterator over binomial coefficients.
structure IterBinomial (T : Type) where
  a : T
  n : T
  k : T

class Integer.AssociatedTypes (Self : Type) where
  [trait_constr_Integer_i0 : num_traits.Num.AssociatedTypes Self]
  [trait_constr_Integer_i1 :
  core_models.cmp.PartialOrd.AssociatedTypes
  Self
  Self]
  [trait_constr_Integer_i2 : core_models.cmp.Ord.AssociatedTypes Self]
  [trait_constr_Integer_i3 : core_models.cmp.Eq.AssociatedTypes Self]

attribute [instance_reducible, instance]
  Integer.AssociatedTypes.trait_constr_Integer_i0

attribute [instance_reducible, instance]
  Integer.AssociatedTypes.trait_constr_Integer_i1

attribute [instance_reducible, instance]
  Integer.AssociatedTypes.trait_constr_Integer_i2

attribute [instance_reducible, instance]
  Integer.AssociatedTypes.trait_constr_Integer_i3

class Integer (Self : Type)
  [associatedTypes : outParam (Integer.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Integer_i0 : num_traits.Num Self]
  [trait_constr_Integer_i1 : core_models.cmp.PartialOrd Self Self]
  [trait_constr_Integer_i2 : core_models.cmp.Ord Self]
  [trait_constr_Integer_i3 : core_models.cmp.Eq Self]
  div_floor (Self) : (Self -> Self -> RustM Self)
  mod_floor (Self) : (Self -> Self -> RustM Self)
  div_ceil (Self) (self : Self) (other : Self) :RustM Self := do
    let ⟨q, r⟩ ← (Integer.div_mod_floor Self self other);
    if (← (num_traits.identities.Zero.is_zero Self r)) then do
      (pure q)
    else do
      (core_models.ops.arith.Add.add
        Self
        Self
        q
        (← (num_traits.identities.One.one Self rust_primitives.hax.Tuple0.mk)))
  gcd (Self) : (Self -> Self -> RustM Self)
  lcm (Self) : (Self -> Self -> RustM Self)
  gcd_lcm (Self) (self : Self) (other : Self) :RustM (rust_primitives.hax.Tuple2
      Self
      Self) := do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (Integer.gcd Self self other))
      (← (Integer.lcm Self self other))))
  extended_gcd (Self)
    [trait_constr_extended_gcd_associated_type_i1 :
      core_models.clone.Clone.AssociatedTypes
      Self]
    [trait_constr_extended_gcd_i1 : core_models.clone.Clone Self ]
    (self : Self)
    (other : Self) :RustM (ExtendedGcd Self) := do
    let s : (rust_primitives.hax.Tuple2 Self Self) :=
      (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero Self rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.One.one Self rust_primitives.hax.Tuple0.mk)));
    let t : (rust_primitives.hax.Tuple2 Self Self) :=
      (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.One.one Self rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero
          Self rust_primitives.hax.Tuple0.mk)));
    let r : (rust_primitives.hax.Tuple2 Self Self) :=
      (rust_primitives.hax.Tuple2.mk
        (← (core_models.clone.Clone.clone Self other))
        (← (core_models.clone.Clone.clone Self self)));
    let ⟨r, s, t⟩ ←
      (rust_primitives.hax.while_loop
        (fun ⟨r, s, t⟩ => (do (pure true) : RustM Bool))
        (fun ⟨r, s, t⟩ =>
          (do
          (!? (← (num_traits.identities.Zero.is_zero
            Self (rust_primitives.hax.Tuple2._0 r)))) :
          RustM Bool))
        (fun ⟨r, s, t⟩ =>
          (do
          (rust_primitives.hax.int.from_machine (0 : u32)) :
          RustM hax_lib.int.Int))
        (rust_primitives.hax.Tuple3.mk r s t)
        (fun ⟨r, s, t⟩ =>
          (do
          let q : Self ←
            (core_models.ops.arith.Div.div
              Self
              Self
              (← (core_models.clone.Clone.clone
                Self (rust_primitives.hax.Tuple2._1 r)))
              (← (core_models.clone.Clone.clone
                Self (rust_primitives.hax.Tuple2._0 r))));
          let
            f : ((rust_primitives.hax.Tuple2 Self Self) ->
            RustM (rust_primitives.hax.Tuple2 Self Self)) :=
            (fun r =>
              (do
              let ⟨_, _⟩ ←
                (core_models.mem.swap Self
                  (rust_primitives.hax.Tuple2._0 r)
                  (rust_primitives.hax.Tuple2._1 r));
              let _ := rust_primitives.hax.Tuple0.mk;
              let r : (rust_primitives.hax.Tuple2 Self Self) :=
                {r
                with _0 := (← (core_models.ops.arith.Sub.sub
                  Self
                  Self
                  (rust_primitives.hax.Tuple2._0 r)
                  (← (core_models.ops.arith.Mul.mul
                    Self
                    Self
                    (← (core_models.clone.Clone.clone Self q))
                    (← (core_models.clone.Clone.clone
                      Self (rust_primitives.hax.Tuple2._1 r)))))))};
              (pure (rust_primitives.hax.Tuple2.mk r r)) :
              RustM
              (rust_primitives.hax.Tuple2
                (rust_primitives.hax.Tuple2 Self Self)
                (rust_primitives.hax.Tuple2 Self Self))));
          let r : (rust_primitives.hax.Tuple2 Self Self) ←
            (core_models.ops.function.Fn.call
              ((rust_primitives.hax.Tuple2 Self Self) ->
              RustM (rust_primitives.hax.Tuple2 Self Self))
              (rust_primitives.hax.Tuple1
                (rust_primitives.hax.Tuple2 Self Self))
              f
              (rust_primitives.hax.Tuple1.mk r));
          let s : (rust_primitives.hax.Tuple2 Self Self) ←
            (core_models.ops.function.Fn.call
              ((rust_primitives.hax.Tuple2 Self Self) ->
              RustM (rust_primitives.hax.Tuple2 Self Self))
              (rust_primitives.hax.Tuple1
                (rust_primitives.hax.Tuple2 Self Self))
              f
              (rust_primitives.hax.Tuple1.mk s));
          let t : (rust_primitives.hax.Tuple2 Self Self) ←
            (core_models.ops.function.Fn.call
              ((rust_primitives.hax.Tuple2 Self Self) ->
              RustM (rust_primitives.hax.Tuple2 Self Self))
              (rust_primitives.hax.Tuple1
                (rust_primitives.hax.Tuple2 Self Self))
              f
              (rust_primitives.hax.Tuple1.mk t));
          (pure (rust_primitives.hax.Tuple3.mk r s t)) :
          RustM
          (rust_primitives.hax.Tuple3
            (rust_primitives.hax.Tuple2 Self Self)
            (rust_primitives.hax.Tuple2 Self Self)
            (rust_primitives.hax.Tuple2 Self Self)))));
    if
    (← (core_models.cmp.PartialOrd.ge
      Self
      Self
      (rust_primitives.hax.Tuple2._1 r)
      (← (num_traits.identities.Zero.zero Self rust_primitives.hax.Tuple0.mk))))
    then do
      (pure (ExtendedGcd.mk
        (gcd := (rust_primitives.hax.Tuple2._1 r))
        (x := (rust_primitives.hax.Tuple2._1 s))
        (y := (rust_primitives.hax.Tuple2._1 t))))
    else do
      (pure (ExtendedGcd.mk
        (gcd := (← (core_models.ops.arith.Sub.sub
          Self
          Self
          (← (num_traits.identities.Zero.zero
            Self rust_primitives.hax.Tuple0.mk))
          (rust_primitives.hax.Tuple2._1 r))))
        (x := (← (core_models.ops.arith.Sub.sub
          Self
          Self
          (← (num_traits.identities.Zero.zero
            Self rust_primitives.hax.Tuple0.mk))
          (rust_primitives.hax.Tuple2._1 s))))
        (y := (← (core_models.ops.arith.Sub.sub
          Self
          Self
          (← (num_traits.identities.Zero.zero
            Self rust_primitives.hax.Tuple0.mk))
          (rust_primitives.hax.Tuple2._1 t))))))
  extended_gcd_lcm (Self)
    [trait_constr_extended_gcd_lcm_associated_type_i1 :
      core_models.clone.Clone.AssociatedTypes
      Self]
    [trait_constr_extended_gcd_lcm_i1 : core_models.clone.Clone Self ]
    [trait_constr_extended_gcd_lcm_associated_type_i2 :
      num_traits.sign.Signed.AssociatedTypes
      Self]
    [trait_constr_extended_gcd_lcm_i2 : num_traits.sign.Signed Self ]
    (self : Self)
    (other : Self) :RustM (rust_primitives.hax.Tuple2 (ExtendedGcd Self) Self)
    := do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (Integer.extended_gcd Self self other))
      (← (Integer.lcm Self self other))))
  divides (Self) (self : Self) (other : Self) :RustM Bool := do
    (Integer.is_multiple_of Self self other)
  is_multiple_of (Self) : (Self -> Self -> RustM Bool)
  is_even (Self) : (Self -> RustM Bool)
  is_odd (Self) : (Self -> RustM Bool)
  div_rem (Self) :
    (Self -> Self -> RustM (rust_primitives.hax.Tuple2 Self Self))
  div_mod_floor (Self) (self : Self) (other : Self) :RustM
    (rust_primitives.hax.Tuple2 Self Self) := do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (Integer.div_floor Self self other))
      (← (Integer.mod_floor Self self other))))
  next_multiple_of (Self)
    [trait_constr_next_multiple_of_associated_type_i1 :
      core_models.clone.Clone.AssociatedTypes
      Self]
    [trait_constr_next_multiple_of_i1 : core_models.clone.Clone Self ]
    (self : Self)
    (other : Self) :RustM Self := do
    let m : Self ← (Integer.mod_floor Self self other);
    (core_models.ops.arith.Add.add
      Self
      Self
      (← (core_models.clone.Clone.clone Self self))
      (← if (← (num_traits.identities.Zero.is_zero Self m)) then do
        (num_traits.identities.Zero.zero Self rust_primitives.hax.Tuple0.mk)
      else do
        (core_models.ops.arith.Sub.sub
          Self
          Self (← (core_models.clone.Clone.clone Self other)) m)))
  prev_multiple_of (Self)
    [trait_constr_prev_multiple_of_associated_type_i1 :
      core_models.clone.Clone.AssociatedTypes
      Self]
    [trait_constr_prev_multiple_of_i1 : core_models.clone.Clone Self ]
    (self : Self)
    (other : Self) :RustM Self := do
    (core_models.ops.arith.Sub.sub
      Self
      Self
      (← (core_models.clone.Clone.clone Self self))
      (← (Integer.mod_floor Self self other)))
  dec (Self)
    [trait_constr_dec_associated_type_i1 :
      core_models.clone.Clone.AssociatedTypes
      Self]
    [trait_constr_dec_i1 : core_models.clone.Clone Self ] (self : Self) :RustM
    Self := do
    let self : Self ←
      (core_models.ops.arith.Sub.sub
        Self
        Self
        (← (core_models.clone.Clone.clone Self self))
        (← (num_traits.identities.One.one Self rust_primitives.hax.Tuple0.mk)));
    (pure self)
  inc (Self)
    [trait_constr_inc_associated_type_i1 :
      core_models.clone.Clone.AssociatedTypes
      Self]
    [trait_constr_inc_i1 : core_models.clone.Clone Self ] (self : Self) :RustM
    Self := do
    let self : Self ←
      (core_models.ops.arith.Add.add
        Self
        Self
        (← (core_models.clone.Clone.clone Self self))
        (← (num_traits.identities.One.one Self rust_primitives.hax.Tuple0.mk)));
    (pure self)

attribute [instance_reducible, instance] Integer.trait_constr_Integer_i0

attribute [instance_reducible, instance] Integer.trait_constr_Integer_i1

attribute [instance_reducible, instance] Integer.trait_constr_Integer_i2

attribute [instance_reducible, instance] Integer.trait_constr_Integer_i3

end num_integer


namespace num_integer.roots

@[spec]
def fixpoint
    (T : Type)
    (F : Type)
    [trait_constr_fixpoint_associated_type_i0 :
      num_integer.Integer.AssociatedTypes
      T]
    [trait_constr_fixpoint_i0 : num_integer.Integer
      T
      (associatedTypes := {
        show num_integer.Integer.AssociatedTypes T
        by infer_instance
        with sorry})]
    [trait_constr_fixpoint_associated_type_i1 :
      core_models.marker.Copy.AssociatedTypes
      T]
    [trait_constr_fixpoint_i1 : core_models.marker.Copy
      T
      (associatedTypes := {
        show core_models.marker.Copy.AssociatedTypes T
        by infer_instance
        with sorry})]
    [trait_constr_fixpoint_associated_type_i2 :
      core_models.ops.function.Fn.AssociatedTypes
      F
      (rust_primitives.hax.Tuple1 T)]
    [trait_constr_fixpoint_i2 : core_models.ops.function.Fn
      F
      (rust_primitives.hax.Tuple1 T)
      (associatedTypes := {
        show
          core_models.ops.function.Fn.AssociatedTypes
          F
          (rust_primitives.hax.Tuple1 T)
        by infer_instance
        with sorry})]
    (x : T)
    (f : F) :
    RustM T := do
  let xn : T ←
    (core_models.ops.function.Fn.call
      F
      (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk x));
  let ⟨x, xn⟩ ←
    (rust_primitives.hax.while_loop
      (fun ⟨x, xn⟩ => (do (pure true) : RustM Bool))
      (fun ⟨x, xn⟩ =>
        (do (core_models.cmp.PartialOrd.lt T T x xn) : RustM Bool))
      (fun ⟨x, xn⟩ =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      (rust_primitives.hax.Tuple2.mk x xn)
      (fun ⟨x, xn⟩ =>
        (do
        let x : T := xn;
        let xn : T ←
          (core_models.ops.function.Fn.call
            F
            (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk x));
        (pure (rust_primitives.hax.Tuple2.mk x xn)) :
        RustM (rust_primitives.hax.Tuple2 T T))));
  let ⟨x, xn⟩ ←
    (rust_primitives.hax.while_loop
      (fun ⟨x, xn⟩ => (do (pure true) : RustM Bool))
      (fun ⟨x, xn⟩ =>
        (do (core_models.cmp.PartialOrd.gt T T x xn) : RustM Bool))
      (fun ⟨x, xn⟩ =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      (rust_primitives.hax.Tuple2.mk x xn)
      (fun ⟨x, xn⟩ =>
        (do
        let x : T := xn;
        let xn : T ←
          (core_models.ops.function.Fn.call
            F
            (rust_primitives.hax.Tuple1 T) f (rust_primitives.hax.Tuple1.mk x));
        (pure (rust_primitives.hax.Tuple2.mk x xn)) :
        RustM (rust_primitives.hax.Tuple2 T T))));
  (pure x)

end num_integer.roots


namespace num_integer.average

--  Provides methods to compute the average of two integers, without overflows.
class Average.AssociatedTypes (Self : Type) where
  [trait_constr_Average_i0 : num_integer.Integer.AssociatedTypes Self]

attribute [instance_reducible, instance]
  Average.AssociatedTypes.trait_constr_Average_i0

class Average (Self : Type)
  [associatedTypes : outParam (Average.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Average_i0 : num_integer.Integer Self]
  average_ceil (Self) : (Self -> Self -> RustM Self)
  average_floor (Self) : (Self -> Self -> RustM Self)

attribute [instance_reducible, instance] Average.trait_constr_Average_i0

@[reducible] instance Impl.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_associated_type_i0 :
    core_models.ops.bit.BitAnd.AssociatedTypes
    I
    I]
  [trait_constr_Impl_i0 : core_models.ops.bit.BitAnd
    I
    I
    (associatedTypes := {
      show core_models.ops.bit.BitAnd.AssociatedTypes I I
      by infer_instance
      with Output := I})]
  [trait_constr_Impl_associated_type_i1 : num_integer.Integer.AssociatedTypes I]
  [trait_constr_Impl_i1 : num_integer.Integer I ]
  [trait_constr_Impl_associated_type_i2 :
    core_models.ops.bit.BitOr.AssociatedTypes
    I
    I]
  [trait_constr_Impl_i2 : core_models.ops.bit.BitOr
    I
    I
    (associatedTypes := {
      show core_models.ops.bit.BitOr.AssociatedTypes I I
      by infer_instance
      with Output := I})]
  [trait_constr_Impl_associated_type_i3 :
    core_models.ops.bit.Shr.AssociatedTypes
    I
    usize]
  [trait_constr_Impl_i3 : core_models.ops.bit.Shr
    I
    usize
    (associatedTypes := {
      show core_models.ops.bit.Shr.AssociatedTypes I usize
      by infer_instance
      with Output := I})]
  [trait_constr_Impl_associated_type_i4 :
    core_models.ops.bit.BitXor.AssociatedTypes
    I
    I]
  [trait_constr_Impl_i4 : core_models.ops.bit.BitXor
    I
    I
    (associatedTypes := {
      show core_models.ops.bit.BitXor.AssociatedTypes I I
      by infer_instance
      with Output := I})] :
  Average.AssociatedTypes I
  where

instance Impl
  (I : Type)
  [trait_constr_Impl_associated_type_i0 :
    core_models.ops.bit.BitAnd.AssociatedTypes
    I
    I]
  [trait_constr_Impl_i0 : core_models.ops.bit.BitAnd
    I
    I
    (associatedTypes := {
      show core_models.ops.bit.BitAnd.AssociatedTypes I I
      by infer_instance
      with Output := I})]
  [trait_constr_Impl_associated_type_i1 : num_integer.Integer.AssociatedTypes I]
  [trait_constr_Impl_i1 : num_integer.Integer I ]
  [trait_constr_Impl_associated_type_i2 :
    core_models.ops.bit.BitOr.AssociatedTypes
    I
    I]
  [trait_constr_Impl_i2 : core_models.ops.bit.BitOr
    I
    I
    (associatedTypes := {
      show core_models.ops.bit.BitOr.AssociatedTypes I I
      by infer_instance
      with Output := I})]
  [trait_constr_Impl_associated_type_i3 :
    core_models.ops.bit.Shr.AssociatedTypes
    I
    usize]
  [trait_constr_Impl_i3 : core_models.ops.bit.Shr
    I
    usize
    (associatedTypes := {
      show core_models.ops.bit.Shr.AssociatedTypes I usize
      by infer_instance
      with Output := I})]
  [trait_constr_Impl_associated_type_i4 :
    core_models.ops.bit.BitXor.AssociatedTypes
    I
    I]
  [trait_constr_Impl_i4 : core_models.ops.bit.BitXor
    I
    I
    (associatedTypes := {
      show core_models.ops.bit.BitXor.AssociatedTypes I I
      by infer_instance
      with Output := I})] :
  Average I
  where
  average_floor := fun (self : I) (other : I) => do
    (core_models.ops.arith.Add.add
      I
      I
      (← (core_models.ops.bit.BitAnd.bitand I I self other))
      (← (core_models.ops.bit.Shr.shr
        I
        usize
        (← (core_models.ops.bit.BitXor.bitxor I I self other))
        (1 : usize))))
  average_ceil := fun (self : I) (other : I) => do
    (core_models.ops.arith.Sub.sub
      I
      I
      (← (core_models.ops.bit.BitOr.bitor I I self other))
      (← (core_models.ops.bit.Shr.shr
        I
        usize
        (← (core_models.ops.bit.BitXor.bitxor I I self other))
        (1 : usize))))

--  Returns the floor value of the average of `x` and `y` --
--  see [Average::average_floor](trait.Average.html#tymethod.average_floor).
@[spec]
def average_floor
    (T : Type)
    [trait_constr_average_floor_associated_type_i0 : Average.AssociatedTypes T]
    [trait_constr_average_floor_i0 : Average T ]
    (x : T)
    (y : T) :
    RustM T := do
  (Average.average_floor T x y)

--  Returns the ceiling value of the average of `x` and `y` --
--  see [Average::average_ceil](trait.Average.html#tymethod.average_ceil).
@[spec]
def average_ceil
    (T : Type)
    [trait_constr_average_ceil_associated_type_i0 : Average.AssociatedTypes T]
    [trait_constr_average_ceil_i0 : Average T ]
    (x : T)
    (y : T) :
    RustM T := do
  (Average.average_ceil T x y)

end num_integer.average


namespace num_integer

--  Simultaneous integer division and modulus
@[spec]
def div_rem
    (T : Type)
    [trait_constr_div_rem_associated_type_i0 : Integer.AssociatedTypes T]
    [trait_constr_div_rem_i0 : Integer T ]
    (x : T)
    (y : T) :
    RustM (rust_primitives.hax.Tuple2 T T) := do
  (Integer.div_rem T x y)

--  Floored integer division
@[spec]
def div_floor
    (T : Type)
    [trait_constr_div_floor_associated_type_i0 : Integer.AssociatedTypes T]
    [trait_constr_div_floor_i0 : Integer T ]
    (x : T)
    (y : T) :
    RustM T := do
  (Integer.div_floor T x y)

--  Floored integer modulus
@[spec]
def mod_floor
    (T : Type)
    [trait_constr_mod_floor_associated_type_i0 : Integer.AssociatedTypes T]
    [trait_constr_mod_floor_i0 : Integer T ]
    (x : T)
    (y : T) :
    RustM T := do
  (Integer.mod_floor T x y)

--  Simultaneous floored integer division and modulus
@[spec]
def div_mod_floor
    (T : Type)
    [trait_constr_div_mod_floor_associated_type_i0 : Integer.AssociatedTypes T]
    [trait_constr_div_mod_floor_i0 : Integer T ]
    (x : T)
    (y : T) :
    RustM (rust_primitives.hax.Tuple2 T T) := do
  (Integer.div_mod_floor T x y)

--  Ceiled integer division
@[spec]
def div_ceil
    (T : Type)
    [trait_constr_div_ceil_associated_type_i0 : Integer.AssociatedTypes T]
    [trait_constr_div_ceil_i0 : Integer T ]
    (x : T)
    (y : T) :
    RustM T := do
  (Integer.div_ceil T x y)

--  Calculates the Greatest Common Divisor (GCD) of the number and `other`. The
--  result is always non-negative.
@[spec]
def gcd
    (T : Type)
    [trait_constr_gcd_associated_type_i0 : Integer.AssociatedTypes T]
    [trait_constr_gcd_i0 : Integer T ]
    (x : T)
    (y : T) :
    RustM T := do
  (Integer.gcd T x y)

--  Calculates the Lowest Common Multiple (LCM) of the number and `other`.
@[spec]
def lcm
    (T : Type)
    [trait_constr_lcm_associated_type_i0 : Integer.AssociatedTypes T]
    [trait_constr_lcm_i0 : Integer T ]
    (x : T)
    (y : T) :
    RustM T := do
  (Integer.lcm T x y)

--  Calculates the Greatest Common Divisor (GCD) and
--  Lowest Common Multiple (LCM) of the number and `other`.
@[spec]
def gcd_lcm
    (T : Type)
    [trait_constr_gcd_lcm_associated_type_i0 : Integer.AssociatedTypes T]
    [trait_constr_gcd_lcm_i0 : Integer T ]
    (x : T)
    (y : T) :
    RustM (rust_primitives.hax.Tuple2 T T) := do
  (Integer.gcd_lcm T x y)

--  For a given n, iterate over all binomial coefficients binomial(n, k), for k=0...n.
-- 
--  Note that this might overflow, depending on `T`. For the primitive
--  integer types, the following n are the largest ones for which there will
--  be no overflow:
-- 
--  type | n
--  -----|---
--  u8   | 10
--  i8   |  9
--  u16  | 18
--  i16  | 17
--  u32  | 34
--  i32  | 33
--  u64  | 67
--  i64  | 66
-- 
--  For larger n, `T` should be a bigint type.
@[spec]
def Impl.new
    (T : Type)
    [trait_constr_new_associated_type_i0 : Integer.AssociatedTypes T]
    [trait_constr_new_i0 : Integer T ]
    (n : T) :
    RustM (IterBinomial T) := do
  (pure (IterBinomial.mk
    (k := (← (num_traits.identities.Zero.zero T rust_primitives.hax.Tuple0.mk)))
    (a := (← (num_traits.identities.One.one T rust_primitives.hax.Tuple0.mk)))
    (n := n)))

--  Calculate r * a / b, avoiding overflows and fractions.
-- 
--  Assumes that b divides r * a evenly.
@[spec]
def multiply_and_divide
    (T : Type)
    [trait_constr_multiply_and_divide_associated_type_i0 :
      Integer.AssociatedTypes
      T]
    [trait_constr_multiply_and_divide_i0 : Integer T ]
    [trait_constr_multiply_and_divide_associated_type_i1 :
      core_models.clone.Clone.AssociatedTypes
      T]
    [trait_constr_multiply_and_divide_i1 : core_models.clone.Clone T ]
    (r : T)
    (a : T)
    (b : T) :
    RustM T := do
  let g : T ←
    (gcd T
      (← (core_models.clone.Clone.clone T r))
      (← (core_models.clone.Clone.clone T b)));
  (core_models.ops.arith.Mul.mul
    T
    T
    (← (core_models.ops.arith.Div.div
      T
      T r (← (core_models.clone.Clone.clone T g))))
    (← (core_models.ops.arith.Div.div
      T
      T a (← (core_models.ops.arith.Div.div T T b g)))))

@[reducible] instance Impl_1.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 : Integer.AssociatedTypes T]
  [trait_constr_Impl_1_i0 : Integer T ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_1_i1 : core_models.clone.Clone T ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (IterBinomial T)
  where
  Item := T

instance Impl_1
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 : Integer.AssociatedTypes T]
  [trait_constr_Impl_1_i0 : Integer T ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_1_i1 : core_models.clone.Clone T ] :
  core_models.iter.traits.iterator.Iterator (IterBinomial T)
  where
  next := fun (self : (IterBinomial T)) => do
    if
    (← (core_models.cmp.PartialOrd.gt
      T
      T (IterBinomial.k self) (IterBinomial.n self))) then do
      (pure (rust_primitives.hax.Tuple2.mk self core_models.option.Option.None))
    else do
      let self : (IterBinomial T) :=
        {self
        with a := (← if
        (← (!? (← (num_traits.identities.Zero.is_zero
          T (IterBinomial.k self))))) then do
          (multiply_and_divide T
            (← (core_models.clone.Clone.clone T (IterBinomial.a self)))
            (← (core_models.ops.arith.Add.add
              T
              T
              (← (core_models.ops.arith.Sub.sub
                T
                T
                (← (core_models.clone.Clone.clone T (IterBinomial.n self)))
                (← (core_models.clone.Clone.clone T (IterBinomial.k self)))))
              (← (num_traits.identities.One.one
                T rust_primitives.hax.Tuple0.mk))))
            (← (core_models.clone.Clone.clone T (IterBinomial.k self))))
        else do
          (num_traits.identities.One.one T rust_primitives.hax.Tuple0.mk))};
      let self : (IterBinomial T) :=
        {self
        with k := (← (core_models.ops.arith.Add.add
          T
          T
          (← (core_models.clone.Clone.clone T (IterBinomial.k self)))
          (← (num_traits.identities.One.one
            T rust_primitives.hax.Tuple0.mk))))};
      let hax_temp_output : (core_models.option.Option T) :=
        (core_models.option.Option.Some
          (← (core_models.clone.Clone.clone T (IterBinomial.a self))));
      (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end num_integer


namespace num_integer.roots

--  Provides methods to compute an integer's square root, cube root,
--  and arbitrary `n`th root.
class Roots.AssociatedTypes (Self : Type) where
  [trait_constr_Roots_i0 : num_integer.Integer.AssociatedTypes Self]

attribute [instance_reducible, instance]
  Roots.AssociatedTypes.trait_constr_Roots_i0

class Roots (Self : Type)
  [associatedTypes : outParam (Roots.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Roots_i0 : num_integer.Integer Self]
  nth_root (Self) : (Self -> u32 -> RustM Self)
  sqrt (Self) (self : Self) :RustM Self := do
    (Roots.nth_root Self self (2 : u32))
  cbrt (Self) (self : Self) :RustM Self := do
    (Roots.nth_root Self self (3 : u32))

attribute [instance_reducible, instance] Roots.trait_constr_Roots_i0

end num_integer.roots


namespace num_integer

@[reducible] instance Impl_8.AssociatedTypes : Integer.AssociatedTypes i8 where

instance Impl_8 : Integer i8 where
  div_floor := fun (self : i8) (other : i8) => do
    let ⟨d, r⟩ ← (Integer.div_rem i8 self other);
    if
    (← ((← ((← (r >? (0 : i8))) &&? (← (other <? (0 : i8)))))
      ||? (← ((← (r <? (0 : i8))) &&? (← (other >? (0 : i8))))))) then do
      (d -? (1 : i8))
    else do
      (pure d)
  mod_floor := fun (self : i8) (other : i8) => do
    let r : i8 ← (self %? other);
    if
    (← ((← ((← (r >? (0 : i8))) &&? (← (other <? (0 : i8)))))
      ||? (← ((← (r <? (0 : i8))) &&? (← (other >? (0 : i8))))))) then do
      (r +? other)
    else do
      (pure r)
  div_mod_floor := fun (self : i8) (other : i8) => do
    let ⟨d, r⟩ ← (Integer.div_rem i8 self other);
    if
    (← ((← ((← (r >? (0 : i8))) &&? (← (other <? (0 : i8)))))
      ||? (← ((← (r <? (0 : i8))) &&? (← (other >? (0 : i8))))))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (d -? (1 : i8)))
        (← (r +? other))))
    else do
      (pure (rust_primitives.hax.Tuple2.mk d r))
  div_ceil := fun (self : i8) (other : i8) => do
    let ⟨d, r⟩ ← (Integer.div_rem i8 self other);
    if
    (← ((← ((← (r >? (0 : i8))) &&? (← (other >? (0 : i8)))))
      ||? (← ((← (r <? (0 : i8))) &&? (← (other <? (0 : i8))))))) then do
      (d +? (1 : i8))
    else do
      (pure d)
  gcd := fun (self : i8) (other : i8) => do
    let m : i8 := self;
    let n : i8 := other;
    if (← ((← (m ==? (0 : i8))) ||? (← (n ==? (0 : i8))))) then do
      (core_models.num.Impl.abs (← (m |||? n)))
    else do
      let shift : u32 ← (core_models.num.Impl.trailing_zeros (← (m |||? n)));
      if
      (← ((← (m
          ==? (← (core_models.num.Impl.min_value
            rust_primitives.hax.Tuple0.mk))))
        ||? (← (n
          ==? (← (core_models.num.Impl.min_value
            rust_primitives.hax.Tuple0.mk)))))) then do
        (num_traits.sign.Signed.abs i8 (← ((1 : i8) <<<? shift)))
      else do
        let m : i8 ← (core_models.num.Impl.abs m);
        let n : i8 ← (core_models.num.Impl.abs n);
        let m : i8 ← (m >>>? (← (core_models.num.Impl.trailing_zeros m)));
        let n : i8 ← (n >>>? (← (core_models.num.Impl.trailing_zeros n)));
        let ⟨m, n⟩ ←
          (rust_primitives.hax.while_loop
            (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
            (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
            (fun ⟨m, n⟩ =>
              (do
              (rust_primitives.hax.int.from_machine (0 : u32)) :
              RustM hax_lib.int.Int))
            (rust_primitives.hax.Tuple2.mk m n)
            (fun ⟨m, n⟩ =>
              (do
              if (← (m >? n)) then do
                let m : i8 ← (m -? n);
                let m : i8 ←
                  (m >>>? (← (core_models.num.Impl.trailing_zeros m)));
                (pure (rust_primitives.hax.Tuple2.mk m n))
              else do
                let n : i8 ← (n -? m);
                let n : i8 ←
                  (n >>>? (← (core_models.num.Impl.trailing_zeros n)));
                (pure (rust_primitives.hax.Tuple2.mk m n)) :
              RustM (rust_primitives.hax.Tuple2 i8 i8))));
        (m <<<? shift)
  extended_gcd_lcm := fun (self : i8) (other : i8) => do
    let egcd : (ExtendedGcd i8) ← (Integer.extended_gcd i8 self other);
    let lcm : i8 ←
      if
      (← (num_traits.identities.Zero.is_zero i8 (ExtendedGcd.gcd egcd))) then do
        (num_traits.identities.Zero.zero i8 rust_primitives.hax.Tuple0.mk)
      else do
        (core_models.num.Impl.abs
          (← (self *? (← (other /? (ExtendedGcd.gcd egcd))))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : i8) (other : i8) => do
    (pure (rust_primitives.hax.Tuple2._1 (← (Integer.gcd_lcm i8 self other))))
  gcd_lcm := fun (self : i8) (other : i8) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero i8 self))
      &&? (← (num_traits.identities.Zero.is_zero i8 other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero i8 rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero i8 rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : i8 ← (Integer.gcd i8 self other);
      let lcm : i8 ←
        (core_models.num.Impl.abs (← (self *? (← (other /? gcd)))));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : i8) (other : i8) => do
    if (← (num_traits.identities.Zero.is_zero i8 other)) then do
      (num_traits.identities.Zero.is_zero i8 self)
    else do
      ((← (self %? other)) ==? (0 : i8))
  is_even := fun (self : i8) => do ((← (self &&&? (1 : i8))) ==? (0 : i8))
  is_odd := fun (self : i8) => do (!? (← (Integer.is_even i8 self)))
  div_rem := fun (self : i8) (other : i8) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))
  next_multiple_of := fun (self : i8) (other : i8) => do
    if (← (other ==? (-1 : i8))) then do
      (pure self)
    else do
      let m : i8 ← (Integer.mod_floor i8 self other);
      (self
        +? (← if (← (m ==? (0 : i8))) then do
          (pure (0 : i8))
        else do
          (other -? m)))
  prev_multiple_of := fun (self : i8) (other : i8) => do
    if (← (other ==? (-1 : i8))) then do
      (pure self)
    else do
      (self -? (← (Integer.mod_floor i8 self other)))

@[reducible] instance Impl_9.AssociatedTypes : Integer.AssociatedTypes i16 where

instance Impl_9 : Integer i16 where
  div_floor := fun (self : i16) (other : i16) => do
    let ⟨d, r⟩ ← (Integer.div_rem i16 self other);
    if
    (← ((← ((← (r >? (0 : i16))) &&? (← (other <? (0 : i16)))))
      ||? (← ((← (r <? (0 : i16))) &&? (← (other >? (0 : i16))))))) then do
      (d -? (1 : i16))
    else do
      (pure d)
  mod_floor := fun (self : i16) (other : i16) => do
    let r : i16 ← (self %? other);
    if
    (← ((← ((← (r >? (0 : i16))) &&? (← (other <? (0 : i16)))))
      ||? (← ((← (r <? (0 : i16))) &&? (← (other >? (0 : i16))))))) then do
      (r +? other)
    else do
      (pure r)
  div_mod_floor := fun (self : i16) (other : i16) => do
    let ⟨d, r⟩ ← (Integer.div_rem i16 self other);
    if
    (← ((← ((← (r >? (0 : i16))) &&? (← (other <? (0 : i16)))))
      ||? (← ((← (r <? (0 : i16))) &&? (← (other >? (0 : i16))))))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (d -? (1 : i16)))
        (← (r +? other))))
    else do
      (pure (rust_primitives.hax.Tuple2.mk d r))
  div_ceil := fun (self : i16) (other : i16) => do
    let ⟨d, r⟩ ← (Integer.div_rem i16 self other);
    if
    (← ((← ((← (r >? (0 : i16))) &&? (← (other >? (0 : i16)))))
      ||? (← ((← (r <? (0 : i16))) &&? (← (other <? (0 : i16))))))) then do
      (d +? (1 : i16))
    else do
      (pure d)
  gcd := fun (self : i16) (other : i16) => do
    let m : i16 := self;
    let n : i16 := other;
    if (← ((← (m ==? (0 : i16))) ||? (← (n ==? (0 : i16))))) then do
      (core_models.num.Impl_1.abs (← (m |||? n)))
    else do
      let shift : u32 ← (core_models.num.Impl_1.trailing_zeros (← (m |||? n)));
      if
      (← ((← (m
          ==? (← (core_models.num.Impl_1.min_value
            rust_primitives.hax.Tuple0.mk))))
        ||? (← (n
          ==? (← (core_models.num.Impl_1.min_value
            rust_primitives.hax.Tuple0.mk)))))) then do
        (num_traits.sign.Signed.abs i16 (← ((1 : i16) <<<? shift)))
      else do
        let m : i16 ← (core_models.num.Impl_1.abs m);
        let n : i16 ← (core_models.num.Impl_1.abs n);
        let m : i16 ← (m >>>? (← (core_models.num.Impl_1.trailing_zeros m)));
        let n : i16 ← (n >>>? (← (core_models.num.Impl_1.trailing_zeros n)));
        let ⟨m, n⟩ ←
          (rust_primitives.hax.while_loop
            (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
            (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
            (fun ⟨m, n⟩ =>
              (do
              (rust_primitives.hax.int.from_machine (0 : u32)) :
              RustM hax_lib.int.Int))
            (rust_primitives.hax.Tuple2.mk m n)
            (fun ⟨m, n⟩ =>
              (do
              if (← (m >? n)) then do
                let m : i16 ← (m -? n);
                let m : i16 ←
                  (m >>>? (← (core_models.num.Impl_1.trailing_zeros m)));
                (pure (rust_primitives.hax.Tuple2.mk m n))
              else do
                let n : i16 ← (n -? m);
                let n : i16 ←
                  (n >>>? (← (core_models.num.Impl_1.trailing_zeros n)));
                (pure (rust_primitives.hax.Tuple2.mk m n)) :
              RustM (rust_primitives.hax.Tuple2 i16 i16))));
        (m <<<? shift)
  extended_gcd_lcm := fun (self : i16) (other : i16) => do
    let egcd : (ExtendedGcd i16) ← (Integer.extended_gcd i16 self other);
    let lcm : i16 ←
      if
      (← (num_traits.identities.Zero.is_zero i16 (ExtendedGcd.gcd egcd))) then
      do
        (num_traits.identities.Zero.zero i16 rust_primitives.hax.Tuple0.mk)
      else do
        (core_models.num.Impl_1.abs
          (← (self *? (← (other /? (ExtendedGcd.gcd egcd))))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : i16) (other : i16) => do
    (pure (rust_primitives.hax.Tuple2._1 (← (Integer.gcd_lcm i16 self other))))
  gcd_lcm := fun (self : i16) (other : i16) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero i16 self))
      &&? (← (num_traits.identities.Zero.is_zero i16 other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero i16 rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero
          i16 rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : i16 ← (Integer.gcd i16 self other);
      let lcm : i16 ←
        (core_models.num.Impl_1.abs (← (self *? (← (other /? gcd)))));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : i16) (other : i16) => do
    if (← (num_traits.identities.Zero.is_zero i16 other)) then do
      (num_traits.identities.Zero.is_zero i16 self)
    else do
      ((← (self %? other)) ==? (0 : i16))
  is_even := fun (self : i16) => do ((← (self &&&? (1 : i16))) ==? (0 : i16))
  is_odd := fun (self : i16) => do (!? (← (Integer.is_even i16 self)))
  div_rem := fun (self : i16) (other : i16) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))
  next_multiple_of := fun (self : i16) (other : i16) => do
    if (← (other ==? (-1 : i16))) then do
      (pure self)
    else do
      let m : i16 ← (Integer.mod_floor i16 self other);
      (self
        +? (← if (← (m ==? (0 : i16))) then do
          (pure (0 : i16))
        else do
          (other -? m)))
  prev_multiple_of := fun (self : i16) (other : i16) => do
    if (← (other ==? (-1 : i16))) then do
      (pure self)
    else do
      (self -? (← (Integer.mod_floor i16 self other)))

@[reducible] instance Impl_10.AssociatedTypes :
  Integer.AssociatedTypes i32
  where

instance Impl_10 : Integer i32 where
  div_floor := fun (self : i32) (other : i32) => do
    let ⟨d, r⟩ ← (Integer.div_rem i32 self other);
    if
    (← ((← ((← (r >? (0 : i32))) &&? (← (other <? (0 : i32)))))
      ||? (← ((← (r <? (0 : i32))) &&? (← (other >? (0 : i32))))))) then do
      (d -? (1 : i32))
    else do
      (pure d)
  mod_floor := fun (self : i32) (other : i32) => do
    let r : i32 ← (self %? other);
    if
    (← ((← ((← (r >? (0 : i32))) &&? (← (other <? (0 : i32)))))
      ||? (← ((← (r <? (0 : i32))) &&? (← (other >? (0 : i32))))))) then do
      (r +? other)
    else do
      (pure r)
  div_mod_floor := fun (self : i32) (other : i32) => do
    let ⟨d, r⟩ ← (Integer.div_rem i32 self other);
    if
    (← ((← ((← (r >? (0 : i32))) &&? (← (other <? (0 : i32)))))
      ||? (← ((← (r <? (0 : i32))) &&? (← (other >? (0 : i32))))))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (d -? (1 : i32)))
        (← (r +? other))))
    else do
      (pure (rust_primitives.hax.Tuple2.mk d r))
  div_ceil := fun (self : i32) (other : i32) => do
    let ⟨d, r⟩ ← (Integer.div_rem i32 self other);
    if
    (← ((← ((← (r >? (0 : i32))) &&? (← (other >? (0 : i32)))))
      ||? (← ((← (r <? (0 : i32))) &&? (← (other <? (0 : i32))))))) then do
      (d +? (1 : i32))
    else do
      (pure d)
  gcd := fun (self : i32) (other : i32) => do
    let m : i32 := self;
    let n : i32 := other;
    if (← ((← (m ==? (0 : i32))) ||? (← (n ==? (0 : i32))))) then do
      (core_models.num.Impl_2.abs (← (m |||? n)))
    else do
      let shift : u32 ← (core_models.num.Impl_2.trailing_zeros (← (m |||? n)));
      if
      (← ((← (m
          ==? (← (core_models.num.Impl_2.min_value
            rust_primitives.hax.Tuple0.mk))))
        ||? (← (n
          ==? (← (core_models.num.Impl_2.min_value
            rust_primitives.hax.Tuple0.mk)))))) then do
        (num_traits.sign.Signed.abs i32 (← ((1 : i32) <<<? shift)))
      else do
        let m : i32 ← (core_models.num.Impl_2.abs m);
        let n : i32 ← (core_models.num.Impl_2.abs n);
        let m : i32 ← (m >>>? (← (core_models.num.Impl_2.trailing_zeros m)));
        let n : i32 ← (n >>>? (← (core_models.num.Impl_2.trailing_zeros n)));
        let ⟨m, n⟩ ←
          (rust_primitives.hax.while_loop
            (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
            (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
            (fun ⟨m, n⟩ =>
              (do
              (rust_primitives.hax.int.from_machine (0 : u32)) :
              RustM hax_lib.int.Int))
            (rust_primitives.hax.Tuple2.mk m n)
            (fun ⟨m, n⟩ =>
              (do
              if (← (m >? n)) then do
                let m : i32 ← (m -? n);
                let m : i32 ←
                  (m >>>? (← (core_models.num.Impl_2.trailing_zeros m)));
                (pure (rust_primitives.hax.Tuple2.mk m n))
              else do
                let n : i32 ← (n -? m);
                let n : i32 ←
                  (n >>>? (← (core_models.num.Impl_2.trailing_zeros n)));
                (pure (rust_primitives.hax.Tuple2.mk m n)) :
              RustM (rust_primitives.hax.Tuple2 i32 i32))));
        (m <<<? shift)
  extended_gcd_lcm := fun (self : i32) (other : i32) => do
    let egcd : (ExtendedGcd i32) ← (Integer.extended_gcd i32 self other);
    let lcm : i32 ←
      if
      (← (num_traits.identities.Zero.is_zero i32 (ExtendedGcd.gcd egcd))) then
      do
        (num_traits.identities.Zero.zero i32 rust_primitives.hax.Tuple0.mk)
      else do
        (core_models.num.Impl_2.abs
          (← (self *? (← (other /? (ExtendedGcd.gcd egcd))))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : i32) (other : i32) => do
    (pure (rust_primitives.hax.Tuple2._1 (← (Integer.gcd_lcm i32 self other))))
  gcd_lcm := fun (self : i32) (other : i32) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero i32 self))
      &&? (← (num_traits.identities.Zero.is_zero i32 other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero i32 rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero
          i32 rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : i32 ← (Integer.gcd i32 self other);
      let lcm : i32 ←
        (core_models.num.Impl_2.abs (← (self *? (← (other /? gcd)))));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : i32) (other : i32) => do
    if (← (num_traits.identities.Zero.is_zero i32 other)) then do
      (num_traits.identities.Zero.is_zero i32 self)
    else do
      ((← (self %? other)) ==? (0 : i32))
  is_even := fun (self : i32) => do ((← (self &&&? (1 : i32))) ==? (0 : i32))
  is_odd := fun (self : i32) => do (!? (← (Integer.is_even i32 self)))
  div_rem := fun (self : i32) (other : i32) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))
  next_multiple_of := fun (self : i32) (other : i32) => do
    if (← (other ==? (-1 : i32))) then do
      (pure self)
    else do
      let m : i32 ← (Integer.mod_floor i32 self other);
      (self
        +? (← if (← (m ==? (0 : i32))) then do
          (pure (0 : i32))
        else do
          (other -? m)))
  prev_multiple_of := fun (self : i32) (other : i32) => do
    if (← (other ==? (-1 : i32))) then do
      (pure self)
    else do
      (self -? (← (Integer.mod_floor i32 self other)))

@[reducible] instance Impl_11.AssociatedTypes :
  Integer.AssociatedTypes i64
  where

instance Impl_11 : Integer i64 where
  div_floor := fun (self : i64) (other : i64) => do
    let ⟨d, r⟩ ← (Integer.div_rem i64 self other);
    if
    (← ((← ((← (r >? (0 : i64))) &&? (← (other <? (0 : i64)))))
      ||? (← ((← (r <? (0 : i64))) &&? (← (other >? (0 : i64))))))) then do
      (d -? (1 : i64))
    else do
      (pure d)
  mod_floor := fun (self : i64) (other : i64) => do
    let r : i64 ← (self %? other);
    if
    (← ((← ((← (r >? (0 : i64))) &&? (← (other <? (0 : i64)))))
      ||? (← ((← (r <? (0 : i64))) &&? (← (other >? (0 : i64))))))) then do
      (r +? other)
    else do
      (pure r)
  div_mod_floor := fun (self : i64) (other : i64) => do
    let ⟨d, r⟩ ← (Integer.div_rem i64 self other);
    if
    (← ((← ((← (r >? (0 : i64))) &&? (← (other <? (0 : i64)))))
      ||? (← ((← (r <? (0 : i64))) &&? (← (other >? (0 : i64))))))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (d -? (1 : i64)))
        (← (r +? other))))
    else do
      (pure (rust_primitives.hax.Tuple2.mk d r))
  div_ceil := fun (self : i64) (other : i64) => do
    let ⟨d, r⟩ ← (Integer.div_rem i64 self other);
    if
    (← ((← ((← (r >? (0 : i64))) &&? (← (other >? (0 : i64)))))
      ||? (← ((← (r <? (0 : i64))) &&? (← (other <? (0 : i64))))))) then do
      (d +? (1 : i64))
    else do
      (pure d)
  gcd := fun (self : i64) (other : i64) => do
    let m : i64 := self;
    let n : i64 := other;
    if (← ((← (m ==? (0 : i64))) ||? (← (n ==? (0 : i64))))) then do
      (core_models.num.Impl_3.abs (← (m |||? n)))
    else do
      let shift : u32 ← (core_models.num.Impl_3.trailing_zeros (← (m |||? n)));
      if
      (← ((← (m
          ==? (← (core_models.num.Impl_3.min_value
            rust_primitives.hax.Tuple0.mk))))
        ||? (← (n
          ==? (← (core_models.num.Impl_3.min_value
            rust_primitives.hax.Tuple0.mk)))))) then do
        (num_traits.sign.Signed.abs i64 (← ((1 : i64) <<<? shift)))
      else do
        let m : i64 ← (core_models.num.Impl_3.abs m);
        let n : i64 ← (core_models.num.Impl_3.abs n);
        let m : i64 ← (m >>>? (← (core_models.num.Impl_3.trailing_zeros m)));
        let n : i64 ← (n >>>? (← (core_models.num.Impl_3.trailing_zeros n)));
        let ⟨m, n⟩ ←
          (rust_primitives.hax.while_loop
            (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
            (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
            (fun ⟨m, n⟩ =>
              (do
              (rust_primitives.hax.int.from_machine (0 : u32)) :
              RustM hax_lib.int.Int))
            (rust_primitives.hax.Tuple2.mk m n)
            (fun ⟨m, n⟩ =>
              (do
              if (← (m >? n)) then do
                let m : i64 ← (m -? n);
                let m : i64 ←
                  (m >>>? (← (core_models.num.Impl_3.trailing_zeros m)));
                (pure (rust_primitives.hax.Tuple2.mk m n))
              else do
                let n : i64 ← (n -? m);
                let n : i64 ←
                  (n >>>? (← (core_models.num.Impl_3.trailing_zeros n)));
                (pure (rust_primitives.hax.Tuple2.mk m n)) :
              RustM (rust_primitives.hax.Tuple2 i64 i64))));
        (m <<<? shift)
  extended_gcd_lcm := fun (self : i64) (other : i64) => do
    let egcd : (ExtendedGcd i64) ← (Integer.extended_gcd i64 self other);
    let lcm : i64 ←
      if
      (← (num_traits.identities.Zero.is_zero i64 (ExtendedGcd.gcd egcd))) then
      do
        (num_traits.identities.Zero.zero i64 rust_primitives.hax.Tuple0.mk)
      else do
        (core_models.num.Impl_3.abs
          (← (self *? (← (other /? (ExtendedGcd.gcd egcd))))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : i64) (other : i64) => do
    (pure (rust_primitives.hax.Tuple2._1 (← (Integer.gcd_lcm i64 self other))))
  gcd_lcm := fun (self : i64) (other : i64) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero i64 self))
      &&? (← (num_traits.identities.Zero.is_zero i64 other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero i64 rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero
          i64 rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : i64 ← (Integer.gcd i64 self other);
      let lcm : i64 ←
        (core_models.num.Impl_3.abs (← (self *? (← (other /? gcd)))));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : i64) (other : i64) => do
    if (← (num_traits.identities.Zero.is_zero i64 other)) then do
      (num_traits.identities.Zero.is_zero i64 self)
    else do
      ((← (self %? other)) ==? (0 : i64))
  is_even := fun (self : i64) => do ((← (self &&&? (1 : i64))) ==? (0 : i64))
  is_odd := fun (self : i64) => do (!? (← (Integer.is_even i64 self)))
  div_rem := fun (self : i64) (other : i64) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))
  next_multiple_of := fun (self : i64) (other : i64) => do
    if (← (other ==? (-1 : i64))) then do
      (pure self)
    else do
      let m : i64 ← (Integer.mod_floor i64 self other);
      (self
        +? (← if (← (m ==? (0 : i64))) then do
          (pure (0 : i64))
        else do
          (other -? m)))
  prev_multiple_of := fun (self : i64) (other : i64) => do
    if (← (other ==? (-1 : i64))) then do
      (pure self)
    else do
      (self -? (← (Integer.mod_floor i64 self other)))

@[reducible] instance Impl_12.AssociatedTypes :
  Integer.AssociatedTypes i128
  where

instance Impl_12 : Integer i128 where
  div_floor := fun (self : i128) (other : i128) => do
    let ⟨d, r⟩ ← (Integer.div_rem i128 self other);
    if
    (← ((← ((← (r >? (0 : i128))) &&? (← (other <? (0 : i128)))))
      ||? (← ((← (r <? (0 : i128))) &&? (← (other >? (0 : i128))))))) then do
      (d -? (1 : i128))
    else do
      (pure d)
  mod_floor := fun (self : i128) (other : i128) => do
    let r : i128 ← (self %? other);
    if
    (← ((← ((← (r >? (0 : i128))) &&? (← (other <? (0 : i128)))))
      ||? (← ((← (r <? (0 : i128))) &&? (← (other >? (0 : i128))))))) then do
      (r +? other)
    else do
      (pure r)
  div_mod_floor := fun (self : i128) (other : i128) => do
    let ⟨d, r⟩ ← (Integer.div_rem i128 self other);
    if
    (← ((← ((← (r >? (0 : i128))) &&? (← (other <? (0 : i128)))))
      ||? (← ((← (r <? (0 : i128))) &&? (← (other >? (0 : i128))))))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (d -? (1 : i128)))
        (← (r +? other))))
    else do
      (pure (rust_primitives.hax.Tuple2.mk d r))
  div_ceil := fun (self : i128) (other : i128) => do
    let ⟨d, r⟩ ← (Integer.div_rem i128 self other);
    if
    (← ((← ((← (r >? (0 : i128))) &&? (← (other >? (0 : i128)))))
      ||? (← ((← (r <? (0 : i128))) &&? (← (other <? (0 : i128))))))) then do
      (d +? (1 : i128))
    else do
      (pure d)
  gcd := fun (self : i128) (other : i128) => do
    let m : i128 := self;
    let n : i128 := other;
    if (← ((← (m ==? (0 : i128))) ||? (← (n ==? (0 : i128))))) then do
      (core_models.num.Impl_4.abs (← (m |||? n)))
    else do
      let shift : u32 ← (core_models.num.Impl_4.trailing_zeros (← (m |||? n)));
      if
      (← ((← (m
          ==? (← (core_models.num.Impl_4.min_value
            rust_primitives.hax.Tuple0.mk))))
        ||? (← (n
          ==? (← (core_models.num.Impl_4.min_value
            rust_primitives.hax.Tuple0.mk)))))) then do
        (num_traits.sign.Signed.abs i128 (← ((1 : i128) <<<? shift)))
      else do
        let m : i128 ← (core_models.num.Impl_4.abs m);
        let n : i128 ← (core_models.num.Impl_4.abs n);
        let m : i128 ← (m >>>? (← (core_models.num.Impl_4.trailing_zeros m)));
        let n : i128 ← (n >>>? (← (core_models.num.Impl_4.trailing_zeros n)));
        let ⟨m, n⟩ ←
          (rust_primitives.hax.while_loop
            (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
            (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
            (fun ⟨m, n⟩ =>
              (do
              (rust_primitives.hax.int.from_machine (0 : u32)) :
              RustM hax_lib.int.Int))
            (rust_primitives.hax.Tuple2.mk m n)
            (fun ⟨m, n⟩ =>
              (do
              if (← (m >? n)) then do
                let m : i128 ← (m -? n);
                let m : i128 ←
                  (m >>>? (← (core_models.num.Impl_4.trailing_zeros m)));
                (pure (rust_primitives.hax.Tuple2.mk m n))
              else do
                let n : i128 ← (n -? m);
                let n : i128 ←
                  (n >>>? (← (core_models.num.Impl_4.trailing_zeros n)));
                (pure (rust_primitives.hax.Tuple2.mk m n)) :
              RustM (rust_primitives.hax.Tuple2 i128 i128))));
        (m <<<? shift)
  extended_gcd_lcm := fun (self : i128) (other : i128) => do
    let egcd : (ExtendedGcd i128) ← (Integer.extended_gcd i128 self other);
    let lcm : i128 ←
      if
      (← (num_traits.identities.Zero.is_zero i128 (ExtendedGcd.gcd egcd))) then
      do
        (num_traits.identities.Zero.zero i128 rust_primitives.hax.Tuple0.mk)
      else do
        (core_models.num.Impl_4.abs
          (← (self *? (← (other /? (ExtendedGcd.gcd egcd))))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : i128) (other : i128) => do
    (pure (rust_primitives.hax.Tuple2._1 (← (Integer.gcd_lcm i128 self other))))
  gcd_lcm := fun (self : i128) (other : i128) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero i128 self))
      &&? (← (num_traits.identities.Zero.is_zero i128 other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero i128 rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero
          i128 rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : i128 ← (Integer.gcd i128 self other);
      let lcm : i128 ←
        (core_models.num.Impl_4.abs (← (self *? (← (other /? gcd)))));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : i128) (other : i128) => do
    if (← (num_traits.identities.Zero.is_zero i128 other)) then do
      (num_traits.identities.Zero.is_zero i128 self)
    else do
      ((← (self %? other)) ==? (0 : i128))
  is_even := fun (self : i128) => do ((← (self &&&? (1 : i128))) ==? (0 : i128))
  is_odd := fun (self : i128) => do (!? (← (Integer.is_even i128 self)))
  div_rem := fun (self : i128) (other : i128) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))
  next_multiple_of := fun (self : i128) (other : i128) => do
    if (← (other ==? (-1 : i128))) then do
      (pure self)
    else do
      let m : i128 ← (Integer.mod_floor i128 self other);
      (self
        +? (← if (← (m ==? (0 : i128))) then do
          (pure (0 : i128))
        else do
          (other -? m)))
  prev_multiple_of := fun (self : i128) (other : i128) => do
    if (← (other ==? (-1 : i128))) then do
      (pure self)
    else do
      (self -? (← (Integer.mod_floor i128 self other)))

@[reducible] instance Impl_13.AssociatedTypes :
  Integer.AssociatedTypes isize
  where

instance Impl_13 : Integer isize where
  div_floor := fun (self : isize) (other : isize) => do
    let ⟨d, r⟩ ← (Integer.div_rem isize self other);
    if
    (← ((← ((← (r >? (0 : isize))) &&? (← (other <? (0 : isize)))))
      ||? (← ((← (r <? (0 : isize))) &&? (← (other >? (0 : isize))))))) then do
      (d -? (1 : isize))
    else do
      (pure d)
  mod_floor := fun (self : isize) (other : isize) => do
    let r : isize ← (self %? other);
    if
    (← ((← ((← (r >? (0 : isize))) &&? (← (other <? (0 : isize)))))
      ||? (← ((← (r <? (0 : isize))) &&? (← (other >? (0 : isize))))))) then do
      (r +? other)
    else do
      (pure r)
  div_mod_floor := fun (self : isize) (other : isize) => do
    let ⟨d, r⟩ ← (Integer.div_rem isize self other);
    if
    (← ((← ((← (r >? (0 : isize))) &&? (← (other <? (0 : isize)))))
      ||? (← ((← (r <? (0 : isize))) &&? (← (other >? (0 : isize))))))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (d -? (1 : isize)))
        (← (r +? other))))
    else do
      (pure (rust_primitives.hax.Tuple2.mk d r))
  div_ceil := fun (self : isize) (other : isize) => do
    let ⟨d, r⟩ ← (Integer.div_rem isize self other);
    if
    (← ((← ((← (r >? (0 : isize))) &&? (← (other >? (0 : isize)))))
      ||? (← ((← (r <? (0 : isize))) &&? (← (other <? (0 : isize))))))) then do
      (d +? (1 : isize))
    else do
      (pure d)
  gcd := fun (self : isize) (other : isize) => do
    let m : isize := self;
    let n : isize := other;
    if (← ((← (m ==? (0 : isize))) ||? (← (n ==? (0 : isize))))) then do
      (core_models.num.Impl_5.abs (← (m |||? n)))
    else do
      let shift : u32 ← (core_models.num.Impl_5.trailing_zeros (← (m |||? n)));
      if
      (← ((← (m
          ==? (← (core_models.num.Impl_5.min_value
            rust_primitives.hax.Tuple0.mk))))
        ||? (← (n
          ==? (← (core_models.num.Impl_5.min_value
            rust_primitives.hax.Tuple0.mk)))))) then do
        (num_traits.sign.Signed.abs isize (← ((1 : isize) <<<? shift)))
      else do
        let m : isize ← (core_models.num.Impl_5.abs m);
        let n : isize ← (core_models.num.Impl_5.abs n);
        let m : isize ← (m >>>? (← (core_models.num.Impl_5.trailing_zeros m)));
        let n : isize ← (n >>>? (← (core_models.num.Impl_5.trailing_zeros n)));
        let ⟨m, n⟩ ←
          (rust_primitives.hax.while_loop
            (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
            (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
            (fun ⟨m, n⟩ =>
              (do
              (rust_primitives.hax.int.from_machine (0 : u32)) :
              RustM hax_lib.int.Int))
            (rust_primitives.hax.Tuple2.mk m n)
            (fun ⟨m, n⟩ =>
              (do
              if (← (m >? n)) then do
                let m : isize ← (m -? n);
                let m : isize ←
                  (m >>>? (← (core_models.num.Impl_5.trailing_zeros m)));
                (pure (rust_primitives.hax.Tuple2.mk m n))
              else do
                let n : isize ← (n -? m);
                let n : isize ←
                  (n >>>? (← (core_models.num.Impl_5.trailing_zeros n)));
                (pure (rust_primitives.hax.Tuple2.mk m n)) :
              RustM (rust_primitives.hax.Tuple2 isize isize))));
        (m <<<? shift)
  extended_gcd_lcm := fun (self : isize) (other : isize) => do
    let egcd : (ExtendedGcd isize) ← (Integer.extended_gcd isize self other);
    let lcm : isize ←
      if
      (← (num_traits.identities.Zero.is_zero isize (ExtendedGcd.gcd egcd))) then
      do
        (num_traits.identities.Zero.zero isize rust_primitives.hax.Tuple0.mk)
      else do
        (core_models.num.Impl_5.abs
          (← (self *? (← (other /? (ExtendedGcd.gcd egcd))))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : isize) (other : isize) => do
    (pure (rust_primitives.hax.Tuple2._1
      (← (Integer.gcd_lcm isize self other))))
  gcd_lcm := fun (self : isize) (other : isize) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero isize self))
      &&? (← (num_traits.identities.Zero.is_zero isize other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero
          isize rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero
          isize rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : isize ← (Integer.gcd isize self other);
      let lcm : isize ←
        (core_models.num.Impl_5.abs (← (self *? (← (other /? gcd)))));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : isize) (other : isize) => do
    if (← (num_traits.identities.Zero.is_zero isize other)) then do
      (num_traits.identities.Zero.is_zero isize self)
    else do
      ((← (self %? other)) ==? (0 : isize))
  is_even := fun (self : isize) => do
    ((← (self &&&? (1 : isize))) ==? (0 : isize))
  is_odd := fun (self : isize) => do (!? (← (Integer.is_even isize self)))
  div_rem := fun (self : isize) (other : isize) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))
  next_multiple_of := fun (self : isize) (other : isize) => do
    if (← (other ==? (-1 : isize))) then do
      (pure self)
    else do
      let m : isize ← (Integer.mod_floor isize self other);
      (self
        +? (← if (← (m ==? (0 : isize))) then do
          (pure (0 : isize))
        else do
          (other -? m)))
  prev_multiple_of := fun (self : isize) (other : isize) => do
    if (← (other ==? (-1 : isize))) then do
      (pure self)
    else do
      (self -? (← (Integer.mod_floor isize self other)))

@[reducible] instance Impl_14.AssociatedTypes : Integer.AssociatedTypes u8 where

instance Impl_14 : Integer u8 where
  div_floor := fun (self : u8) (other : u8) => do (self /? other)
  mod_floor := fun (self : u8) (other : u8) => do (self %? other)
  div_ceil := fun (self : u8) (other : u8) => do
    ((← (self /? other))
      +? (← (rust_primitives.hax.cast_op
        (← ((0 : u8) !=? (← (self %? other)))) :
        RustM u8)))
  gcd := fun (self : u8) (other : u8) => do
    let m : u8 := self;
    let n : u8 := other;
    if (← ((← (m ==? (0 : u8))) ||? (← (n ==? (0 : u8))))) then do
      (m |||? n)
    else do
      let shift : u32 ← (core_models.num.Impl_6.trailing_zeros (← (m |||? n)));
      let m : u8 ← (m >>>? (← (core_models.num.Impl_6.trailing_zeros m)));
      let n : u8 ← (n >>>? (← (core_models.num.Impl_6.trailing_zeros n)));
      let ⟨m, n⟩ ←
        (rust_primitives.hax.while_loop
          (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
          (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
          (fun ⟨m, n⟩ =>
            (do
            (rust_primitives.hax.int.from_machine (0 : u32)) :
            RustM hax_lib.int.Int))
          (rust_primitives.hax.Tuple2.mk m n)
          (fun ⟨m, n⟩ =>
            (do
            if (← (m >? n)) then do
              let m : u8 ← (m -? n);
              let m : u8 ←
                (m >>>? (← (core_models.num.Impl_6.trailing_zeros m)));
              (pure (rust_primitives.hax.Tuple2.mk m n))
            else do
              let n : u8 ← (n -? m);
              let n : u8 ←
                (n >>>? (← (core_models.num.Impl_6.trailing_zeros n)));
              (pure (rust_primitives.hax.Tuple2.mk m n)) :
            RustM (rust_primitives.hax.Tuple2 u8 u8))));
      (m <<<? shift)
  extended_gcd_lcm := fun (self : u8) (other : u8) => do
    let egcd : (ExtendedGcd u8) ← (Integer.extended_gcd u8 self other);
    let lcm : u8 ←
      if
      (← (num_traits.identities.Zero.is_zero u8 (ExtendedGcd.gcd egcd))) then do
        (num_traits.identities.Zero.zero u8 rust_primitives.hax.Tuple0.mk)
      else do
        (self *? (← (other /? (ExtendedGcd.gcd egcd))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : u8) (other : u8) => do
    (pure (rust_primitives.hax.Tuple2._1 (← (Integer.gcd_lcm u8 self other))))
  gcd_lcm := fun (self : u8) (other : u8) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero u8 self))
      &&? (← (num_traits.identities.Zero.is_zero u8 other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero u8 rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero u8 rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : u8 ← (Integer.gcd u8 self other);
      let lcm : u8 ← (self *? (← (other /? gcd)));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : u8) (other : u8) => do
    if (← (num_traits.identities.Zero.is_zero u8 other)) then do
      (num_traits.identities.Zero.is_zero u8 self)
    else do
      ((← (self %? other)) ==? (0 : u8))
  is_even := fun (self : u8) => do ((← (self %? (2 : u8))) ==? (0 : u8))
  is_odd := fun (self : u8) => do (!? (← (Integer.is_even u8 self)))
  div_rem := fun (self : u8) (other : u8) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))

@[reducible] instance Impl_15.AssociatedTypes :
  Integer.AssociatedTypes u16
  where

instance Impl_15 : Integer u16 where
  div_floor := fun (self : u16) (other : u16) => do (self /? other)
  mod_floor := fun (self : u16) (other : u16) => do (self %? other)
  div_ceil := fun (self : u16) (other : u16) => do
    ((← (self /? other))
      +? (← (rust_primitives.hax.cast_op
        (← ((0 : u16) !=? (← (self %? other)))) :
        RustM u16)))
  gcd := fun (self : u16) (other : u16) => do
    let m : u16 := self;
    let n : u16 := other;
    if (← ((← (m ==? (0 : u16))) ||? (← (n ==? (0 : u16))))) then do
      (m |||? n)
    else do
      let shift : u32 ← (core_models.num.Impl_7.trailing_zeros (← (m |||? n)));
      let m : u16 ← (m >>>? (← (core_models.num.Impl_7.trailing_zeros m)));
      let n : u16 ← (n >>>? (← (core_models.num.Impl_7.trailing_zeros n)));
      let ⟨m, n⟩ ←
        (rust_primitives.hax.while_loop
          (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
          (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
          (fun ⟨m, n⟩ =>
            (do
            (rust_primitives.hax.int.from_machine (0 : u32)) :
            RustM hax_lib.int.Int))
          (rust_primitives.hax.Tuple2.mk m n)
          (fun ⟨m, n⟩ =>
            (do
            if (← (m >? n)) then do
              let m : u16 ← (m -? n);
              let m : u16 ←
                (m >>>? (← (core_models.num.Impl_7.trailing_zeros m)));
              (pure (rust_primitives.hax.Tuple2.mk m n))
            else do
              let n : u16 ← (n -? m);
              let n : u16 ←
                (n >>>? (← (core_models.num.Impl_7.trailing_zeros n)));
              (pure (rust_primitives.hax.Tuple2.mk m n)) :
            RustM (rust_primitives.hax.Tuple2 u16 u16))));
      (m <<<? shift)
  extended_gcd_lcm := fun (self : u16) (other : u16) => do
    let egcd : (ExtendedGcd u16) ← (Integer.extended_gcd u16 self other);
    let lcm : u16 ←
      if
      (← (num_traits.identities.Zero.is_zero u16 (ExtendedGcd.gcd egcd))) then
      do
        (num_traits.identities.Zero.zero u16 rust_primitives.hax.Tuple0.mk)
      else do
        (self *? (← (other /? (ExtendedGcd.gcd egcd))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : u16) (other : u16) => do
    (pure (rust_primitives.hax.Tuple2._1 (← (Integer.gcd_lcm u16 self other))))
  gcd_lcm := fun (self : u16) (other : u16) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero u16 self))
      &&? (← (num_traits.identities.Zero.is_zero u16 other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero u16 rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero
          u16 rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : u16 ← (Integer.gcd u16 self other);
      let lcm : u16 ← (self *? (← (other /? gcd)));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : u16) (other : u16) => do
    if (← (num_traits.identities.Zero.is_zero u16 other)) then do
      (num_traits.identities.Zero.is_zero u16 self)
    else do
      ((← (self %? other)) ==? (0 : u16))
  is_even := fun (self : u16) => do ((← (self %? (2 : u16))) ==? (0 : u16))
  is_odd := fun (self : u16) => do (!? (← (Integer.is_even u16 self)))
  div_rem := fun (self : u16) (other : u16) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))

@[reducible] instance Impl_16.AssociatedTypes :
  Integer.AssociatedTypes u32
  where

instance Impl_16 : Integer u32 where
  div_floor := fun (self : u32) (other : u32) => do (self /? other)
  mod_floor := fun (self : u32) (other : u32) => do (self %? other)
  div_ceil := fun (self : u32) (other : u32) => do
    ((← (self /? other))
      +? (← (rust_primitives.hax.cast_op
        (← ((0 : u32) !=? (← (self %? other)))) :
        RustM u32)))
  gcd := fun (self : u32) (other : u32) => do
    let m : u32 := self;
    let n : u32 := other;
    if (← ((← (m ==? (0 : u32))) ||? (← (n ==? (0 : u32))))) then do
      (m |||? n)
    else do
      let shift : u32 ← (core_models.num.Impl_8.trailing_zeros (← (m |||? n)));
      let m : u32 ← (m >>>? (← (core_models.num.Impl_8.trailing_zeros m)));
      let n : u32 ← (n >>>? (← (core_models.num.Impl_8.trailing_zeros n)));
      let ⟨m, n⟩ ←
        (rust_primitives.hax.while_loop
          (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
          (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
          (fun ⟨m, n⟩ =>
            (do
            (rust_primitives.hax.int.from_machine (0 : u32)) :
            RustM hax_lib.int.Int))
          (rust_primitives.hax.Tuple2.mk m n)
          (fun ⟨m, n⟩ =>
            (do
            if (← (m >? n)) then do
              let m : u32 ← (m -? n);
              let m : u32 ←
                (m >>>? (← (core_models.num.Impl_8.trailing_zeros m)));
              (pure (rust_primitives.hax.Tuple2.mk m n))
            else do
              let n : u32 ← (n -? m);
              let n : u32 ←
                (n >>>? (← (core_models.num.Impl_8.trailing_zeros n)));
              (pure (rust_primitives.hax.Tuple2.mk m n)) :
            RustM (rust_primitives.hax.Tuple2 u32 u32))));
      (m <<<? shift)
  extended_gcd_lcm := fun (self : u32) (other : u32) => do
    let egcd : (ExtendedGcd u32) ← (Integer.extended_gcd u32 self other);
    let lcm : u32 ←
      if
      (← (num_traits.identities.Zero.is_zero u32 (ExtendedGcd.gcd egcd))) then
      do
        (num_traits.identities.Zero.zero u32 rust_primitives.hax.Tuple0.mk)
      else do
        (self *? (← (other /? (ExtendedGcd.gcd egcd))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : u32) (other : u32) => do
    (pure (rust_primitives.hax.Tuple2._1 (← (Integer.gcd_lcm u32 self other))))
  gcd_lcm := fun (self : u32) (other : u32) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero u32 self))
      &&? (← (num_traits.identities.Zero.is_zero u32 other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero u32 rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero
          u32 rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : u32 ← (Integer.gcd u32 self other);
      let lcm : u32 ← (self *? (← (other /? gcd)));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : u32) (other : u32) => do
    if (← (num_traits.identities.Zero.is_zero u32 other)) then do
      (num_traits.identities.Zero.is_zero u32 self)
    else do
      ((← (self %? other)) ==? (0 : u32))
  is_even := fun (self : u32) => do ((← (self %? (2 : u32))) ==? (0 : u32))
  is_odd := fun (self : u32) => do (!? (← (Integer.is_even u32 self)))
  div_rem := fun (self : u32) (other : u32) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))

@[reducible] instance Impl_17.AssociatedTypes :
  Integer.AssociatedTypes u64
  where

instance Impl_17 : Integer u64 where
  div_floor := fun (self : u64) (other : u64) => do (self /? other)
  mod_floor := fun (self : u64) (other : u64) => do (self %? other)
  div_ceil := fun (self : u64) (other : u64) => do
    ((← (self /? other))
      +? (← (rust_primitives.hax.cast_op
        (← ((0 : u64) !=? (← (self %? other)))) :
        RustM u64)))
  gcd := fun (self : u64) (other : u64) => do
    let m : u64 := self;
    let n : u64 := other;
    if (← ((← (m ==? (0 : u64))) ||? (← (n ==? (0 : u64))))) then do
      (m |||? n)
    else do
      let shift : u32 ← (core_models.num.Impl_9.trailing_zeros (← (m |||? n)));
      let m : u64 ← (m >>>? (← (core_models.num.Impl_9.trailing_zeros m)));
      let n : u64 ← (n >>>? (← (core_models.num.Impl_9.trailing_zeros n)));
      let ⟨m, n⟩ ←
        (rust_primitives.hax.while_loop
          (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
          (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
          (fun ⟨m, n⟩ =>
            (do
            (rust_primitives.hax.int.from_machine (0 : u32)) :
            RustM hax_lib.int.Int))
          (rust_primitives.hax.Tuple2.mk m n)
          (fun ⟨m, n⟩ =>
            (do
            if (← (m >? n)) then do
              let m : u64 ← (m -? n);
              let m : u64 ←
                (m >>>? (← (core_models.num.Impl_9.trailing_zeros m)));
              (pure (rust_primitives.hax.Tuple2.mk m n))
            else do
              let n : u64 ← (n -? m);
              let n : u64 ←
                (n >>>? (← (core_models.num.Impl_9.trailing_zeros n)));
              (pure (rust_primitives.hax.Tuple2.mk m n)) :
            RustM (rust_primitives.hax.Tuple2 u64 u64))));
      (m <<<? shift)
  extended_gcd_lcm := fun (self : u64) (other : u64) => do
    let egcd : (ExtendedGcd u64) ← (Integer.extended_gcd u64 self other);
    let lcm : u64 ←
      if
      (← (num_traits.identities.Zero.is_zero u64 (ExtendedGcd.gcd egcd))) then
      do
        (num_traits.identities.Zero.zero u64 rust_primitives.hax.Tuple0.mk)
      else do
        (self *? (← (other /? (ExtendedGcd.gcd egcd))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : u64) (other : u64) => do
    (pure (rust_primitives.hax.Tuple2._1 (← (Integer.gcd_lcm u64 self other))))
  gcd_lcm := fun (self : u64) (other : u64) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero u64 self))
      &&? (← (num_traits.identities.Zero.is_zero u64 other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero u64 rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero
          u64 rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : u64 ← (Integer.gcd u64 self other);
      let lcm : u64 ← (self *? (← (other /? gcd)));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : u64) (other : u64) => do
    if (← (num_traits.identities.Zero.is_zero u64 other)) then do
      (num_traits.identities.Zero.is_zero u64 self)
    else do
      ((← (self %? other)) ==? (0 : u64))
  is_even := fun (self : u64) => do ((← (self %? (2 : u64))) ==? (0 : u64))
  is_odd := fun (self : u64) => do (!? (← (Integer.is_even u64 self)))
  div_rem := fun (self : u64) (other : u64) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))

@[reducible] instance Impl_18.AssociatedTypes :
  Integer.AssociatedTypes u128
  where

instance Impl_18 : Integer u128 where
  div_floor := fun (self : u128) (other : u128) => do (self /? other)
  mod_floor := fun (self : u128) (other : u128) => do (self %? other)
  div_ceil := fun (self : u128) (other : u128) => do
    ((← (self /? other))
      +? (← (rust_primitives.hax.cast_op
        (← ((0 : u128) !=? (← (self %? other)))) :
        RustM u128)))
  gcd := fun (self : u128) (other : u128) => do
    let m : u128 := self;
    let n : u128 := other;
    if (← ((← (m ==? (0 : u128))) ||? (← (n ==? (0 : u128))))) then do
      (m |||? n)
    else do
      let shift : u32 ← (core_models.num.Impl_10.trailing_zeros (← (m |||? n)));
      let m : u128 ← (m >>>? (← (core_models.num.Impl_10.trailing_zeros m)));
      let n : u128 ← (n >>>? (← (core_models.num.Impl_10.trailing_zeros n)));
      let ⟨m, n⟩ ←
        (rust_primitives.hax.while_loop
          (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
          (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
          (fun ⟨m, n⟩ =>
            (do
            (rust_primitives.hax.int.from_machine (0 : u32)) :
            RustM hax_lib.int.Int))
          (rust_primitives.hax.Tuple2.mk m n)
          (fun ⟨m, n⟩ =>
            (do
            if (← (m >? n)) then do
              let m : u128 ← (m -? n);
              let m : u128 ←
                (m >>>? (← (core_models.num.Impl_10.trailing_zeros m)));
              (pure (rust_primitives.hax.Tuple2.mk m n))
            else do
              let n : u128 ← (n -? m);
              let n : u128 ←
                (n >>>? (← (core_models.num.Impl_10.trailing_zeros n)));
              (pure (rust_primitives.hax.Tuple2.mk m n)) :
            RustM (rust_primitives.hax.Tuple2 u128 u128))));
      (m <<<? shift)
  extended_gcd_lcm := fun (self : u128) (other : u128) => do
    let egcd : (ExtendedGcd u128) ← (Integer.extended_gcd u128 self other);
    let lcm : u128 ←
      if
      (← (num_traits.identities.Zero.is_zero u128 (ExtendedGcd.gcd egcd))) then
      do
        (num_traits.identities.Zero.zero u128 rust_primitives.hax.Tuple0.mk)
      else do
        (self *? (← (other /? (ExtendedGcd.gcd egcd))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : u128) (other : u128) => do
    (pure (rust_primitives.hax.Tuple2._1 (← (Integer.gcd_lcm u128 self other))))
  gcd_lcm := fun (self : u128) (other : u128) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero u128 self))
      &&? (← (num_traits.identities.Zero.is_zero u128 other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero u128 rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero
          u128 rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : u128 ← (Integer.gcd u128 self other);
      let lcm : u128 ← (self *? (← (other /? gcd)));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : u128) (other : u128) => do
    if (← (num_traits.identities.Zero.is_zero u128 other)) then do
      (num_traits.identities.Zero.is_zero u128 self)
    else do
      ((← (self %? other)) ==? (0 : u128))
  is_even := fun (self : u128) => do ((← (self %? (2 : u128))) ==? (0 : u128))
  is_odd := fun (self : u128) => do (!? (← (Integer.is_even u128 self)))
  div_rem := fun (self : u128) (other : u128) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))

@[reducible] instance Impl_19.AssociatedTypes :
  Integer.AssociatedTypes usize
  where

instance Impl_19 : Integer usize where
  div_floor := fun (self : usize) (other : usize) => do (self /? other)
  mod_floor := fun (self : usize) (other : usize) => do (self %? other)
  div_ceil := fun (self : usize) (other : usize) => do
    ((← (self /? other))
      +? (← (rust_primitives.hax.cast_op
        (← ((0 : usize) !=? (← (self %? other)))) :
        RustM usize)))
  gcd := fun (self : usize) (other : usize) => do
    let m : usize := self;
    let n : usize := other;
    if (← ((← (m ==? (0 : usize))) ||? (← (n ==? (0 : usize))))) then do
      (m |||? n)
    else do
      let shift : u32 ← (core_models.num.Impl_11.trailing_zeros (← (m |||? n)));
      let m : usize ← (m >>>? (← (core_models.num.Impl_11.trailing_zeros m)));
      let n : usize ← (n >>>? (← (core_models.num.Impl_11.trailing_zeros n)));
      let ⟨m, n⟩ ←
        (rust_primitives.hax.while_loop
          (fun ⟨m, n⟩ => (do (pure true) : RustM Bool))
          (fun ⟨m, n⟩ => (do (m !=? n) : RustM Bool))
          (fun ⟨m, n⟩ =>
            (do
            (rust_primitives.hax.int.from_machine (0 : u32)) :
            RustM hax_lib.int.Int))
          (rust_primitives.hax.Tuple2.mk m n)
          (fun ⟨m, n⟩ =>
            (do
            if (← (m >? n)) then do
              let m : usize ← (m -? n);
              let m : usize ←
                (m >>>? (← (core_models.num.Impl_11.trailing_zeros m)));
              (pure (rust_primitives.hax.Tuple2.mk m n))
            else do
              let n : usize ← (n -? m);
              let n : usize ←
                (n >>>? (← (core_models.num.Impl_11.trailing_zeros n)));
              (pure (rust_primitives.hax.Tuple2.mk m n)) :
            RustM (rust_primitives.hax.Tuple2 usize usize))));
      (m <<<? shift)
  extended_gcd_lcm := fun (self : usize) (other : usize) => do
    let egcd : (ExtendedGcd usize) ← (Integer.extended_gcd usize self other);
    let lcm : usize ←
      if
      (← (num_traits.identities.Zero.is_zero usize (ExtendedGcd.gcd egcd))) then
      do
        (num_traits.identities.Zero.zero usize rust_primitives.hax.Tuple0.mk)
      else do
        (self *? (← (other /? (ExtendedGcd.gcd egcd))));
    (pure (rust_primitives.hax.Tuple2.mk egcd lcm))
  lcm := fun (self : usize) (other : usize) => do
    (pure (rust_primitives.hax.Tuple2._1
      (← (Integer.gcd_lcm usize self other))))
  gcd_lcm := fun (self : usize) (other : usize) => do
    if
    (← ((← (num_traits.identities.Zero.is_zero usize self))
      &&? (← (num_traits.identities.Zero.is_zero usize other)))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (num_traits.identities.Zero.zero
          usize rust_primitives.hax.Tuple0.mk))
        (← (num_traits.identities.Zero.zero
          usize rust_primitives.hax.Tuple0.mk))))
    else do
      let gcd : usize ← (Integer.gcd usize self other);
      let lcm : usize ← (self *? (← (other /? gcd)));
      (pure (rust_primitives.hax.Tuple2.mk gcd lcm))
  is_multiple_of := fun (self : usize) (other : usize) => do
    if (← (num_traits.identities.Zero.is_zero usize other)) then do
      (num_traits.identities.Zero.is_zero usize self)
    else do
      ((← (self %? other)) ==? (0 : usize))
  is_even := fun (self : usize) => do
    ((← (self %? (2 : usize))) ==? (0 : usize))
  is_odd := fun (self : usize) => do (!? (← (Integer.is_even usize self)))
  div_rem := fun (self : usize) (other : usize) => do
    (pure (rust_primitives.hax.Tuple2.mk
      (← (self /? other))
      (← (self %? other))))

--  Calculate the binomial coefficient.
-- 
--  Note that this might overflow, depending on `T`. For the primitive integer
--  types, the following n are the largest ones possible such that there will
--  be no overflow for any k:
-- 
--  type | n
--  -----|---
--  u8   | 10
--  i8   |  9
--  u16  | 18
--  i16  | 17
--  u32  | 34
--  i32  | 33
--  u64  | 67
--  i64  | 66
-- 
--  For larger n, consider using a bigint type for `T`.
@[spec]
def binomial
    (T : Type)
    [trait_constr_binomial_associated_type_i0 : Integer.AssociatedTypes T]
    [trait_constr_binomial_i0 : Integer T ]
    [trait_constr_binomial_associated_type_i1 :
      core_models.clone.Clone.AssociatedTypes
      T]
    [trait_constr_binomial_i1 : core_models.clone.Clone T ]
    (n : T)
    (k : T) :
    RustM T := do
  if (← (core_models.cmp.PartialOrd.gt T T k n)) then do
    (num_traits.identities.Zero.zero T rust_primitives.hax.Tuple0.mk)
  else do
    if
    (← (core_models.cmp.PartialOrd.gt
      T
      T
      k
      (← (core_models.ops.arith.Sub.sub
        T
        T
        (← (core_models.clone.Clone.clone T n))
        (← (core_models.clone.Clone.clone T k)))))) then do
      (binomial T
        (← (core_models.clone.Clone.clone T n))
        (← (core_models.ops.arith.Sub.sub T T n k)))
    else do
      let r : T ←
        (num_traits.identities.One.one T rust_primitives.hax.Tuple0.mk);
      let d : T ←
        (num_traits.identities.One.one T rust_primitives.hax.Tuple0.mk);
      let ⟨d, n, r⟩ := sorry;
      (pure r)
partial_fixpoint

end num_integer


namespace num_integer.roots

--  Returns the truncated principal square root of an integer --
--  see [Roots::sqrt](trait.Roots.html#method.sqrt).
@[spec]
def sqrt
    (T : Type)
    [trait_constr_sqrt_associated_type_i0 : Roots.AssociatedTypes T]
    [trait_constr_sqrt_i0 : Roots T ]
    (x : T) :
    RustM T := do
  (Roots.sqrt T x)

--  Returns the truncated principal cube root of an integer --
--  see [Roots::cbrt](trait.Roots.html#method.cbrt).
@[spec]
def cbrt
    (T : Type)
    [trait_constr_cbrt_associated_type_i0 : Roots.AssociatedTypes T]
    [trait_constr_cbrt_i0 : Roots T ]
    (x : T) :
    RustM T := do
  (Roots.cbrt T x)

--  Returns the truncated principal `n`th root of an integer --
--  see [Roots::nth_root](trait.Roots.html#tymethod.nth_root).
@[spec]
def nth_root
    (T : Type)
    [trait_constr_nth_root_associated_type_i0 : Roots.AssociatedTypes T]
    [trait_constr_nth_root_i0 : Roots T ]
    (x : T)
    (n : u32) :
    RustM T := do
  (Roots.nth_root T x n)

end num_integer.roots


namespace num_integer

--  Calculate the multinomial coefficient.
@[spec]
def multinomial
    (T : Type)
    [trait_constr_multinomial_associated_type_i0 : Integer.AssociatedTypes T]
    [trait_constr_multinomial_i0 : Integer T ]
    [trait_constr_multinomial_associated_type_i1 :
      core_models.clone.Clone.AssociatedTypes
      T]
    [trait_constr_multinomial_i1 : core_models.clone.Clone T ]
    [trait_constr_multinomial_associated_type_i2 :
      core_models.ops.arith.Add.AssociatedTypes
      T
      T]
    [trait_constr_multinomial_i2 : core_models.ops.arith.Add
      T
      T
      (associatedTypes := {
        show core_models.ops.arith.Add.AssociatedTypes T T
        by infer_instance
        with Output := T})]
    (k : (RustSlice T)) :
    RustM T := do
  let r : T ← (num_traits.identities.One.one T rust_primitives.hax.Tuple0.mk);
  let p : T ← (num_traits.identities.Zero.zero T rust_primitives.hax.Tuple0.mk);
  let ⟨p, r⟩ ←
    (core_models.iter.traits.iterator.Iterator.fold
      (← (core_models.iter.traits.collect.IntoIterator.into_iter
        (RustSlice T) k))
      (rust_primitives.hax.Tuple2.mk p r)
      (fun ⟨p, r⟩ i =>
        (do
        let p : T ← (core_models.ops.arith.Add.add T T p i);
        let r : T ←
          (core_models.ops.arith.Mul.mul
            T
            T
            r
            (← (binomial T
              (← (core_models.clone.Clone.clone T p))
              (← (core_models.clone.Clone.clone T i)))));
        (pure (rust_primitives.hax.Tuple2.mk p r)) :
        RustM (rust_primitives.hax.Tuple2 T T))));
  (pure r)

end num_integer


namespace num_integer.roots

@[reducible] instance Impl_3.AssociatedTypes : Roots.AssociatedTypes i64 where

instance Impl_3 : Roots i64 where
  nth_root := fun (self : i64) (n : u32) => do
    if (← (self >=? (0 : i64))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          u64 (← (rust_primitives.hax.cast_op self : RustM u64)) n)) :
        RustM i64)
    else do
      let _ ← (hax_lib.assert (← (num_integer.Integer.is_odd u32 n)));
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          u64
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl_3.wrapping_neg self)) :
            RustM u64))
          n)) :
        RustM i64)))
  sqrt := fun (self : i64) => do
    let _ ← (hax_lib.assert (← (self >=? (0 : i64))));
    (rust_primitives.hax.cast_op
      (← (Roots.sqrt u64 (← (rust_primitives.hax.cast_op self : RustM u64)))) :
      RustM i64)
  cbrt := fun (self : i64) => do
    if (← (self >=? (0 : i64))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.cbrt u64 (← (rust_primitives.hax.cast_op self : RustM u64))))
        :
        RustM i64)
    else do
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.cbrt
          u64
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl_3.wrapping_neg self)) :
            RustM u64)))) :
        RustM i64)))

@[spec]
def Impl_9.sqrt.go (a : u64) : RustM u64 := do
  if (← ((← (bits u64 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if (← (a <=? core_models.legacy_int_modules.u64.MAX)) then do
      (Roots.sqrt u64 a)
    else do
      let lo : u64 ←
        ((← (Roots.sqrt u64 (← (a >>>? (2 : u32))))) <<<? (1 : i32));
      let hi : u64 ← (lo +? (1 : u64));
      if (← ((← (hi *? hi)) <=? a)) then do (pure hi) else do (pure lo)
  else do
    if (← (a <? (4 : u64))) then do
      (rust_primitives.hax.cast_op (← (a >? (0 : u64))) : RustM u64)
    else do
      let next : (u64 -> RustM u64) :=
        (fun x => (do ((← ((← (a /? x)) +? x)) >>>? (1 : i32)) : RustM u64));
      (fixpoint u64 (u64 -> RustM u64) (← (Impl_9.sqrt.go.guess a)) next)

@[spec]
def Impl_9.nth_root.go (a : u64) (n : u32) : RustM u64 := do
  match n with
    | 0 => do
      let _ ←
        (rust_primitives.hax.never_to_any
          (← (core_models.panicking.panic "can\'t find a root of degree 0!")));
      if
      (← ((← ((← (bits u64 rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : u64) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u64))) : RustM u64)
      else do
        if
        (← ((← (bits u64 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
          if (← (a <=? core_models.legacy_int_modules.u64.MAX)) then do
            (Roots.nth_root u64 a n)
          else do
            let lo : u64 ←
              ((← (Roots.nth_root u64 (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : u64 ← (lo +? (1 : u64));
            if
            (← ((← ((← (core_models.num.Impl_9.trailing_zeros
                  (← (core_models.num.Impl_9.next_power_of_two hi))))
                *? n))
              >=? (← (bits u64 rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow u64
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_9.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (u64 -> RustM u64) :=
            (fun x =>
              (do
              let y : u64 ←
                match
                  (← (num_traits.pow.checked_pow u64
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : u64));
              ((← (y
                  +? (← (x
                    *? (← (rust_primitives.hax.cast_op n1 : RustM u64))))))
                /? (← (rust_primitives.hax.cast_op n : RustM u64))) :
              RustM u64));
          (fixpoint u64 (u64 -> RustM u64)
            (← (Impl_9.nth_root.go.guess a n))
            next)
    | 1 => do (pure a)
    | 2 => do (Roots.sqrt u64 a)
    | 3 => do (Roots.cbrt u64 a)
    | _ => do
      let _ := rust_primitives.hax.Tuple0.mk;
      if
      (← ((← ((← (bits u64 rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : u64) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u64))) : RustM u64)
      else do
        if
        (← ((← (bits u64 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
          if (← (a <=? core_models.legacy_int_modules.u64.MAX)) then do
            (Roots.nth_root u64 a n)
          else do
            let lo : u64 ←
              ((← (Roots.nth_root u64 (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : u64 ← (lo +? (1 : u64));
            if
            (← ((← ((← (core_models.num.Impl_9.trailing_zeros
                  (← (core_models.num.Impl_9.next_power_of_two hi))))
                *? n))
              >=? (← (bits u64 rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow u64
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_9.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (u64 -> RustM u64) :=
            (fun x =>
              (do
              let y : u64 ←
                match
                  (← (num_traits.pow.checked_pow u64
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : u64));
              ((← (y
                  +? (← (x
                    *? (← (rust_primitives.hax.cast_op n1 : RustM u64))))))
                /? (← (rust_primitives.hax.cast_op n : RustM u64))) :
              RustM u64));
          (fixpoint u64 (u64 -> RustM u64)
            (← (Impl_9.nth_root.go.guess a n))
            next)

@[spec]
def Impl_9.cbrt.go (a : u64) : RustM u64 := do
  if (← ((← (bits u64 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if (← (a <=? core_models.legacy_int_modules.u64.MAX)) then do
      (Roots.cbrt u64 a)
    else do
      let lo : u64 ←
        ((← (Roots.cbrt u64 (← (a >>>? (3 : u32))))) <<<? (1 : i32));
      let hi : u64 ← (lo +? (1 : u64));
      if (← ((← ((← (hi *? hi)) *? hi)) <=? a)) then do
        (pure hi)
      else do
        (pure lo)
  else do
    if (← ((← (bits u64 rust_primitives.hax.Tuple0.mk)) <=? (32 : u32))) then do
      let x : u64 := a;
      let y2 : u64 := (0 : u64);
      let y : u64 := (0 : u64);
      let smax : u32 ←
        ((← (bits u64 rust_primitives.hax.Tuple0.mk)) /? (3 : u32));
      let ⟨x, y, y2⟩ ←
        (core_models.iter.traits.iterator.Iterator.fold
          (← (core_models.iter.traits.collect.IntoIterator.into_iter
            (core_models.iter.adapters.rev.Rev
              (core_models.ops.range.Range u32))
            (← (core_models.iter.traits.iterator.Iterator.rev
              (core_models.ops.range.Range u32)
              (core_models.ops.range.Range.mk
                (start := (0 : u32))
                (_end := (← (smax +? (1 : u32)))))))))
          (rust_primitives.hax.Tuple3.mk x y y2)
          (fun ⟨x, y, y2⟩ s =>
            (do
            let s : u32 ← (s *? (3 : u32));
            let y2 : u64 ← (y2 *? (4 : u64));
            let y : u64 ← (y *? (2 : u64));
            let b : u64 ← ((← ((3 : u64) *? (← (y2 +? y)))) +? (1 : u64));
            if (← ((← (x >>>? s)) >=? b)) then do
              let x : u64 ← (x -? (← (b <<<? s)));
              let y2 : u64 ← (y2 +? (← ((← ((2 : u64) *? y)) +? (1 : u64))));
              let y : u64 ← (y +? (1 : u64));
              (pure (rust_primitives.hax.Tuple3.mk x y y2))
            else do
              (pure (rust_primitives.hax.Tuple3.mk x y y2)) :
            RustM (rust_primitives.hax.Tuple3 u64 u64 u64))));
      (pure y)
    else do
      if (← (a <? (8 : u64))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u64))) : RustM u64)
      else do
        if
        (← (a
          <=? (← (rust_primitives.hax.cast_op
            core_models.legacy_int_modules.u32.MAX :
            RustM u64)))) then do
          (rust_primitives.hax.cast_op
            (← (Roots.cbrt u32 (← (rust_primitives.hax.cast_op a : RustM u32))))
            :
            RustM u64)
        else do
          let next : (u64 -> RustM u64) :=
            (fun x =>
              (do
              ((← ((← (a /? (← (x *? x)))) +? (← (x *? (2 : u64)))))
                /? (3 : u64)) :
              RustM u64));
          (fixpoint u64 (u64 -> RustM u64) (← (Impl_9.cbrt.go.guess a)) next)

@[reducible] instance Impl_9.AssociatedTypes : Roots.AssociatedTypes u64 where

instance Impl_9 : Roots u64 where
  nth_root := fun (self : u64) (n : u32) => do (Impl_9.nth_root.go self n)
  sqrt := fun (self : u64) => do (Impl_9.sqrt.go self)
  cbrt := fun (self : u64) => do (Impl_9.cbrt.go self)

@[spec]
def Impl_8.sqrt.go (a : u32) : RustM u32 := do
  if (← ((← (bits u32 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if
    (← (a
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u64.MAX :
        RustM u32)))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.sqrt u64 (← (rust_primitives.hax.cast_op a : RustM u64)))) :
        RustM u32)
    else do
      let lo : u32 ←
        ((← (Roots.sqrt u32 (← (a >>>? (2 : u32))))) <<<? (1 : i32));
      let hi : u32 ← (lo +? (1 : u32));
      if (← ((← (hi *? hi)) <=? a)) then do (pure hi) else do (pure lo)
  else do
    if (← (a <? (4 : u32))) then do
      (rust_primitives.hax.cast_op (← (a >? (0 : u32))) : RustM u32)
    else do
      let next : (u32 -> RustM u32) :=
        (fun x => (do ((← ((← (a /? x)) +? x)) >>>? (1 : i32)) : RustM u32));
      (fixpoint u32 (u32 -> RustM u32) (← (Impl_8.sqrt.go.guess a)) next)

@[spec]
def Impl_8.nth_root.go (a : u32) (n : u32) : RustM u32 := do
  match n with
    | 0 => do
      let _ ←
        (rust_primitives.hax.never_to_any
          (← (core_models.panicking.panic "can\'t find a root of degree 0!")));
      if
      (← ((← ((← (bits u32 rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : u32) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u32))) : RustM u32)
      else do
        if
        (← ((← (bits u32 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
          if
          (← (a
            <=? (← (rust_primitives.hax.cast_op
              core_models.legacy_int_modules.u64.MAX :
              RustM u32)))) then do
            (rust_primitives.hax.cast_op
              (← (Roots.nth_root
                u64 (← (rust_primitives.hax.cast_op a : RustM u64)) n)) :
              RustM u32)
          else do
            let lo : u32 ←
              ((← (Roots.nth_root u32 (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : u32 ← (lo +? (1 : u32));
            if
            (← ((← ((← (core_models.num.Impl_8.trailing_zeros
                  (← (core_models.num.Impl_8.next_power_of_two hi))))
                *? n))
              >=? (← (bits u32 rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow u32
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_8.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (u32 -> RustM u32) :=
            (fun x =>
              (do
              let y : u32 ←
                match
                  (← (num_traits.pow.checked_pow u32
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : u32));
              ((← (y +? (← (x *? n1)))) /? n) :
              RustM u32));
          (fixpoint u32 (u32 -> RustM u32)
            (← (Impl_8.nth_root.go.guess a n))
            next)
    | 1 => do (pure a)
    | 2 => do (Roots.sqrt u32 a)
    | 3 => do (Roots.cbrt u32 a)
    | _ => do
      let _ := rust_primitives.hax.Tuple0.mk;
      if
      (← ((← ((← (bits u32 rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : u32) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u32))) : RustM u32)
      else do
        if
        (← ((← (bits u32 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
          if
          (← (a
            <=? (← (rust_primitives.hax.cast_op
              core_models.legacy_int_modules.u64.MAX :
              RustM u32)))) then do
            (rust_primitives.hax.cast_op
              (← (Roots.nth_root
                u64 (← (rust_primitives.hax.cast_op a : RustM u64)) n)) :
              RustM u32)
          else do
            let lo : u32 ←
              ((← (Roots.nth_root u32 (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : u32 ← (lo +? (1 : u32));
            if
            (← ((← ((← (core_models.num.Impl_8.trailing_zeros
                  (← (core_models.num.Impl_8.next_power_of_two hi))))
                *? n))
              >=? (← (bits u32 rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow u32
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_8.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (u32 -> RustM u32) :=
            (fun x =>
              (do
              let y : u32 ←
                match
                  (← (num_traits.pow.checked_pow u32
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : u32));
              ((← (y +? (← (x *? n1)))) /? n) :
              RustM u32));
          (fixpoint u32 (u32 -> RustM u32)
            (← (Impl_8.nth_root.go.guess a n))
            next)

@[spec]
def Impl_8.cbrt.go (a : u32) : RustM u32 := do
  if (← ((← (bits u32 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if
    (← (a
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u64.MAX :
        RustM u32)))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.cbrt u64 (← (rust_primitives.hax.cast_op a : RustM u64)))) :
        RustM u32)
    else do
      let lo : u32 ←
        ((← (Roots.cbrt u32 (← (a >>>? (3 : u32))))) <<<? (1 : i32));
      let hi : u32 ← (lo +? (1 : u32));
      if (← ((← ((← (hi *? hi)) *? hi)) <=? a)) then do
        (pure hi)
      else do
        (pure lo)
  else do
    if (← ((← (bits u32 rust_primitives.hax.Tuple0.mk)) <=? (32 : u32))) then do
      let x : u32 := a;
      let y2 : u32 := (0 : u32);
      let y : u32 := (0 : u32);
      let smax : u32 ←
        ((← (bits u32 rust_primitives.hax.Tuple0.mk)) /? (3 : u32));
      let ⟨x, y, y2⟩ ←
        (core_models.iter.traits.iterator.Iterator.fold
          (← (core_models.iter.traits.collect.IntoIterator.into_iter
            (core_models.iter.adapters.rev.Rev
              (core_models.ops.range.Range u32))
            (← (core_models.iter.traits.iterator.Iterator.rev
              (core_models.ops.range.Range u32)
              (core_models.ops.range.Range.mk
                (start := (0 : u32))
                (_end := (← (smax +? (1 : u32)))))))))
          (rust_primitives.hax.Tuple3.mk x y y2)
          (fun ⟨x, y, y2⟩ s =>
            (do
            let s : u32 ← (s *? (3 : u32));
            let y2 : u32 ← (y2 *? (4 : u32));
            let y : u32 ← (y *? (2 : u32));
            let b : u32 ← ((← ((3 : u32) *? (← (y2 +? y)))) +? (1 : u32));
            if (← ((← (x >>>? s)) >=? b)) then do
              let x : u32 ← (x -? (← (b <<<? s)));
              let y2 : u32 ← (y2 +? (← ((← ((2 : u32) *? y)) +? (1 : u32))));
              let y : u32 ← (y +? (1 : u32));
              (pure (rust_primitives.hax.Tuple3.mk x y y2))
            else do
              (pure (rust_primitives.hax.Tuple3.mk x y y2)) :
            RustM (rust_primitives.hax.Tuple3 u32 u32 u32))));
      (pure y)
    else do
      if (← (a <? (8 : u32))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u32))) : RustM u32)
      else do
        if (← (a <=? core_models.legacy_int_modules.u32.MAX)) then do
          (Roots.cbrt u32 a)
        else do
          let next : (u32 -> RustM u32) :=
            (fun x =>
              (do
              ((← ((← (a /? (← (x *? x)))) +? (← (x *? (2 : u32)))))
                /? (3 : u32)) :
              RustM u32));
          (fixpoint u32 (u32 -> RustM u32) (← (Impl_8.cbrt.go.guess a)) next)

@[reducible] instance Impl_8.AssociatedTypes : Roots.AssociatedTypes u32 where

instance Impl_8 : Roots u32 where
  nth_root := fun (self : u32) (n : u32) => do (Impl_8.nth_root.go self n)
  sqrt := fun (self : u32) => do (Impl_8.sqrt.go self)
  cbrt := fun (self : u32) => do (Impl_8.cbrt.go self)

@[reducible] instance Impl_2.AssociatedTypes : Roots.AssociatedTypes i32 where

instance Impl_2 : Roots i32 where
  nth_root := fun (self : i32) (n : u32) => do
    if (← (self >=? (0 : i32))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          u32 (← (rust_primitives.hax.cast_op self : RustM u32)) n)) :
        RustM i32)
    else do
      let _ ← (hax_lib.assert (← (num_integer.Integer.is_odd u32 n)));
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          u32
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl_2.wrapping_neg self)) :
            RustM u32))
          n)) :
        RustM i32)))
  sqrt := fun (self : i32) => do
    let _ ← (hax_lib.assert (← (self >=? (0 : i32))));
    (rust_primitives.hax.cast_op
      (← (Roots.sqrt u32 (← (rust_primitives.hax.cast_op self : RustM u32)))) :
      RustM i32)
  cbrt := fun (self : i32) => do
    if (← (self >=? (0 : i32))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.cbrt u32 (← (rust_primitives.hax.cast_op self : RustM u32))))
        :
        RustM i32)
    else do
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.cbrt
          u32
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl_2.wrapping_neg self)) :
            RustM u32)))) :
        RustM i32)))

@[spec]
def Impl_6.sqrt.go (a : u8) : RustM u8 := do
  if (← ((← (bits u8 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if
    (← (a
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u64.MAX :
        RustM u8)))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.sqrt u64 (← (rust_primitives.hax.cast_op a : RustM u64)))) :
        RustM u8)
    else do
      let lo : u8 ← ((← (Roots.sqrt u8 (← (a >>>? (2 : u32))))) <<<? (1 : i32));
      let hi : u8 ← (lo +? (1 : u8));
      if (← ((← (hi *? hi)) <=? a)) then do (pure hi) else do (pure lo)
  else do
    if (← (a <? (4 : u8))) then do
      (rust_primitives.hax.cast_op (← (a >? (0 : u8))) : RustM u8)
    else do
      let next : (u8 -> RustM u8) :=
        (fun x => (do ((← ((← (a /? x)) +? x)) >>>? (1 : i32)) : RustM u8));
      (fixpoint u8 (u8 -> RustM u8) (← (Impl_6.sqrt.go.guess a)) next)

@[spec]
def Impl_6.nth_root.go (a : u8) (n : u32) : RustM u8 := do
  match n with
    | 0 => do
      let _ ←
        (rust_primitives.hax.never_to_any
          (← (core_models.panicking.panic "can\'t find a root of degree 0!")));
      if
      (← ((← ((← (bits u8 rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : u8) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u8))) : RustM u8)
      else do
        if
        (← ((← (bits u8 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
          if
          (← (a
            <=? (← (rust_primitives.hax.cast_op
              core_models.legacy_int_modules.u64.MAX :
              RustM u8)))) then do
            (rust_primitives.hax.cast_op
              (← (Roots.nth_root
                u64 (← (rust_primitives.hax.cast_op a : RustM u64)) n)) :
              RustM u8)
          else do
            let lo : u8 ←
              ((← (Roots.nth_root u8 (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : u8 ← (lo +? (1 : u8));
            if
            (← ((← ((← (core_models.num.Impl_6.trailing_zeros
                  (← (core_models.num.Impl_6.next_power_of_two hi))))
                *? n))
              >=? (← (bits u8 rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow u8
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_6.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (u8 -> RustM u8) :=
            (fun x =>
              (do
              let y : u8 ←
                match
                  (← (num_traits.pow.checked_pow u8
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : u8));
              ((← (y
                  +? (← (x
                    *? (← (rust_primitives.hax.cast_op n1 : RustM u8))))))
                /? (← (rust_primitives.hax.cast_op n : RustM u8))) :
              RustM u8));
          (fixpoint u8 (u8 -> RustM u8) (← (Impl_6.nth_root.go.guess a n)) next)
    | 1 => do (pure a)
    | 2 => do (Roots.sqrt u8 a)
    | 3 => do (Roots.cbrt u8 a)
    | _ => do
      let _ := rust_primitives.hax.Tuple0.mk;
      if
      (← ((← ((← (bits u8 rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : u8) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u8))) : RustM u8)
      else do
        if
        (← ((← (bits u8 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
          if
          (← (a
            <=? (← (rust_primitives.hax.cast_op
              core_models.legacy_int_modules.u64.MAX :
              RustM u8)))) then do
            (rust_primitives.hax.cast_op
              (← (Roots.nth_root
                u64 (← (rust_primitives.hax.cast_op a : RustM u64)) n)) :
              RustM u8)
          else do
            let lo : u8 ←
              ((← (Roots.nth_root u8 (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : u8 ← (lo +? (1 : u8));
            if
            (← ((← ((← (core_models.num.Impl_6.trailing_zeros
                  (← (core_models.num.Impl_6.next_power_of_two hi))))
                *? n))
              >=? (← (bits u8 rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow u8
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_6.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (u8 -> RustM u8) :=
            (fun x =>
              (do
              let y : u8 ←
                match
                  (← (num_traits.pow.checked_pow u8
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : u8));
              ((← (y
                  +? (← (x
                    *? (← (rust_primitives.hax.cast_op n1 : RustM u8))))))
                /? (← (rust_primitives.hax.cast_op n : RustM u8))) :
              RustM u8));
          (fixpoint u8 (u8 -> RustM u8) (← (Impl_6.nth_root.go.guess a n)) next)

@[spec]
def Impl_6.cbrt.go (a : u8) : RustM u8 := do
  if (← ((← (bits u8 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if
    (← (a
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u64.MAX :
        RustM u8)))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.cbrt u64 (← (rust_primitives.hax.cast_op a : RustM u64)))) :
        RustM u8)
    else do
      let lo : u8 ← ((← (Roots.cbrt u8 (← (a >>>? (3 : u32))))) <<<? (1 : i32));
      let hi : u8 ← (lo +? (1 : u8));
      if (← ((← ((← (hi *? hi)) *? hi)) <=? a)) then do
        (pure hi)
      else do
        (pure lo)
  else do
    if (← ((← (bits u8 rust_primitives.hax.Tuple0.mk)) <=? (32 : u32))) then do
      let x : u8 := a;
      let y2 : u8 := (0 : u8);
      let y : u8 := (0 : u8);
      let smax : u32 ←
        ((← (bits u8 rust_primitives.hax.Tuple0.mk)) /? (3 : u32));
      let ⟨x, y, y2⟩ ←
        (core_models.iter.traits.iterator.Iterator.fold
          (← (core_models.iter.traits.collect.IntoIterator.into_iter
            (core_models.iter.adapters.rev.Rev
              (core_models.ops.range.Range u32))
            (← (core_models.iter.traits.iterator.Iterator.rev
              (core_models.ops.range.Range u32)
              (core_models.ops.range.Range.mk
                (start := (0 : u32))
                (_end := (← (smax +? (1 : u32)))))))))
          (rust_primitives.hax.Tuple3.mk x y y2)
          (fun ⟨x, y, y2⟩ s =>
            (do
            let s : u32 ← (s *? (3 : u32));
            let y2 : u8 ← (y2 *? (4 : u8));
            let y : u8 ← (y *? (2 : u8));
            let b : u8 ← ((← ((3 : u8) *? (← (y2 +? y)))) +? (1 : u8));
            if (← ((← (x >>>? s)) >=? b)) then do
              let x : u8 ← (x -? (← (b <<<? s)));
              let y2 : u8 ← (y2 +? (← ((← ((2 : u8) *? y)) +? (1 : u8))));
              let y : u8 ← (y +? (1 : u8));
              (pure (rust_primitives.hax.Tuple3.mk x y y2))
            else do
              (pure (rust_primitives.hax.Tuple3.mk x y y2)) :
            RustM (rust_primitives.hax.Tuple3 u8 u8 u8))));
      (pure y)
    else do
      if (← (a <? (8 : u8))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u8))) : RustM u8)
      else do
        if
        (← (a
          <=? (← (rust_primitives.hax.cast_op
            core_models.legacy_int_modules.u32.MAX :
            RustM u8)))) then do
          (rust_primitives.hax.cast_op
            (← (Roots.cbrt u32 (← (rust_primitives.hax.cast_op a : RustM u32))))
            :
            RustM u8)
        else do
          let next : (u8 -> RustM u8) :=
            (fun x =>
              (do
              ((← ((← (a /? (← (x *? x)))) +? (← (x *? (2 : u8))))) /? (3 : u8))
              :
              RustM u8));
          (fixpoint u8 (u8 -> RustM u8) (← (Impl_6.cbrt.go.guess a)) next)

@[reducible] instance Impl_6.AssociatedTypes : Roots.AssociatedTypes u8 where

instance Impl_6 : Roots u8 where
  nth_root := fun (self : u8) (n : u32) => do (Impl_6.nth_root.go self n)
  sqrt := fun (self : u8) => do (Impl_6.sqrt.go self)
  cbrt := fun (self : u8) => do (Impl_6.cbrt.go self)

@[reducible] instance Impl.AssociatedTypes : Roots.AssociatedTypes i8 where

instance Impl : Roots i8 where
  nth_root := fun (self : i8) (n : u32) => do
    if (← (self >=? (0 : i8))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          u8 (← (rust_primitives.hax.cast_op self : RustM u8)) n)) :
        RustM i8)
    else do
      let _ ← (hax_lib.assert (← (num_integer.Integer.is_odd u32 n)));
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          u8
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl.wrapping_neg self)) :
            RustM u8))
          n)) :
        RustM i8)))
  sqrt := fun (self : i8) => do
    let _ ← (hax_lib.assert (← (self >=? (0 : i8))));
    (rust_primitives.hax.cast_op
      (← (Roots.sqrt u8 (← (rust_primitives.hax.cast_op self : RustM u8)))) :
      RustM i8)
  cbrt := fun (self : i8) => do
    if (← (self >=? (0 : i8))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.cbrt u8 (← (rust_primitives.hax.cast_op self : RustM u8)))) :
        RustM i8)
    else do
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.cbrt
          u8
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl.wrapping_neg self)) :
            RustM u8)))) :
        RustM i8)))

@[spec]
def Impl_7.sqrt.go (a : u16) : RustM u16 := do
  if (← ((← (bits u16 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if
    (← (a
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u64.MAX :
        RustM u16)))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.sqrt u64 (← (rust_primitives.hax.cast_op a : RustM u64)))) :
        RustM u16)
    else do
      let lo : u16 ←
        ((← (Roots.sqrt u16 (← (a >>>? (2 : u32))))) <<<? (1 : i32));
      let hi : u16 ← (lo +? (1 : u16));
      if (← ((← (hi *? hi)) <=? a)) then do (pure hi) else do (pure lo)
  else do
    if (← (a <? (4 : u16))) then do
      (rust_primitives.hax.cast_op (← (a >? (0 : u16))) : RustM u16)
    else do
      let next : (u16 -> RustM u16) :=
        (fun x => (do ((← ((← (a /? x)) +? x)) >>>? (1 : i32)) : RustM u16));
      (fixpoint u16 (u16 -> RustM u16) (← (Impl_7.sqrt.go.guess a)) next)

@[spec]
def Impl_7.nth_root.go (a : u16) (n : u32) : RustM u16 := do
  match n with
    | 0 => do
      let _ ←
        (rust_primitives.hax.never_to_any
          (← (core_models.panicking.panic "can\'t find a root of degree 0!")));
      if
      (← ((← ((← (bits u16 rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : u16) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u16))) : RustM u16)
      else do
        if
        (← ((← (bits u16 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
          if
          (← (a
            <=? (← (rust_primitives.hax.cast_op
              core_models.legacy_int_modules.u64.MAX :
              RustM u16)))) then do
            (rust_primitives.hax.cast_op
              (← (Roots.nth_root
                u64 (← (rust_primitives.hax.cast_op a : RustM u64)) n)) :
              RustM u16)
          else do
            let lo : u16 ←
              ((← (Roots.nth_root u16 (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : u16 ← (lo +? (1 : u16));
            if
            (← ((← ((← (core_models.num.Impl_7.trailing_zeros
                  (← (core_models.num.Impl_7.next_power_of_two hi))))
                *? n))
              >=? (← (bits u16 rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow u16
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_7.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (u16 -> RustM u16) :=
            (fun x =>
              (do
              let y : u16 ←
                match
                  (← (num_traits.pow.checked_pow u16
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : u16));
              ((← (y
                  +? (← (x
                    *? (← (rust_primitives.hax.cast_op n1 : RustM u16))))))
                /? (← (rust_primitives.hax.cast_op n : RustM u16))) :
              RustM u16));
          (fixpoint u16 (u16 -> RustM u16)
            (← (Impl_7.nth_root.go.guess a n))
            next)
    | 1 => do (pure a)
    | 2 => do (Roots.sqrt u16 a)
    | 3 => do (Roots.cbrt u16 a)
    | _ => do
      let _ := rust_primitives.hax.Tuple0.mk;
      if
      (← ((← ((← (bits u16 rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : u16) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u16))) : RustM u16)
      else do
        if
        (← ((← (bits u16 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
          if
          (← (a
            <=? (← (rust_primitives.hax.cast_op
              core_models.legacy_int_modules.u64.MAX :
              RustM u16)))) then do
            (rust_primitives.hax.cast_op
              (← (Roots.nth_root
                u64 (← (rust_primitives.hax.cast_op a : RustM u64)) n)) :
              RustM u16)
          else do
            let lo : u16 ←
              ((← (Roots.nth_root u16 (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : u16 ← (lo +? (1 : u16));
            if
            (← ((← ((← (core_models.num.Impl_7.trailing_zeros
                  (← (core_models.num.Impl_7.next_power_of_two hi))))
                *? n))
              >=? (← (bits u16 rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow u16
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_7.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (u16 -> RustM u16) :=
            (fun x =>
              (do
              let y : u16 ←
                match
                  (← (num_traits.pow.checked_pow u16
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : u16));
              ((← (y
                  +? (← (x
                    *? (← (rust_primitives.hax.cast_op n1 : RustM u16))))))
                /? (← (rust_primitives.hax.cast_op n : RustM u16))) :
              RustM u16));
          (fixpoint u16 (u16 -> RustM u16)
            (← (Impl_7.nth_root.go.guess a n))
            next)

@[spec]
def Impl_7.cbrt.go (a : u16) : RustM u16 := do
  if (← ((← (bits u16 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if
    (← (a
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u64.MAX :
        RustM u16)))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.cbrt u64 (← (rust_primitives.hax.cast_op a : RustM u64)))) :
        RustM u16)
    else do
      let lo : u16 ←
        ((← (Roots.cbrt u16 (← (a >>>? (3 : u32))))) <<<? (1 : i32));
      let hi : u16 ← (lo +? (1 : u16));
      if (← ((← ((← (hi *? hi)) *? hi)) <=? a)) then do
        (pure hi)
      else do
        (pure lo)
  else do
    if (← ((← (bits u16 rust_primitives.hax.Tuple0.mk)) <=? (32 : u32))) then do
      let x : u16 := a;
      let y2 : u16 := (0 : u16);
      let y : u16 := (0 : u16);
      let smax : u32 ←
        ((← (bits u16 rust_primitives.hax.Tuple0.mk)) /? (3 : u32));
      let ⟨x, y, y2⟩ ←
        (core_models.iter.traits.iterator.Iterator.fold
          (← (core_models.iter.traits.collect.IntoIterator.into_iter
            (core_models.iter.adapters.rev.Rev
              (core_models.ops.range.Range u32))
            (← (core_models.iter.traits.iterator.Iterator.rev
              (core_models.ops.range.Range u32)
              (core_models.ops.range.Range.mk
                (start := (0 : u32))
                (_end := (← (smax +? (1 : u32)))))))))
          (rust_primitives.hax.Tuple3.mk x y y2)
          (fun ⟨x, y, y2⟩ s =>
            (do
            let s : u32 ← (s *? (3 : u32));
            let y2 : u16 ← (y2 *? (4 : u16));
            let y : u16 ← (y *? (2 : u16));
            let b : u16 ← ((← ((3 : u16) *? (← (y2 +? y)))) +? (1 : u16));
            if (← ((← (x >>>? s)) >=? b)) then do
              let x : u16 ← (x -? (← (b <<<? s)));
              let y2 : u16 ← (y2 +? (← ((← ((2 : u16) *? y)) +? (1 : u16))));
              let y : u16 ← (y +? (1 : u16));
              (pure (rust_primitives.hax.Tuple3.mk x y y2))
            else do
              (pure (rust_primitives.hax.Tuple3.mk x y y2)) :
            RustM (rust_primitives.hax.Tuple3 u16 u16 u16))));
      (pure y)
    else do
      if (← (a <? (8 : u16))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u16))) : RustM u16)
      else do
        if
        (← (a
          <=? (← (rust_primitives.hax.cast_op
            core_models.legacy_int_modules.u32.MAX :
            RustM u16)))) then do
          (rust_primitives.hax.cast_op
            (← (Roots.cbrt u32 (← (rust_primitives.hax.cast_op a : RustM u32))))
            :
            RustM u16)
        else do
          let next : (u16 -> RustM u16) :=
            (fun x =>
              (do
              ((← ((← (a /? (← (x *? x)))) +? (← (x *? (2 : u16)))))
                /? (3 : u16)) :
              RustM u16));
          (fixpoint u16 (u16 -> RustM u16) (← (Impl_7.cbrt.go.guess a)) next)

@[reducible] instance Impl_7.AssociatedTypes : Roots.AssociatedTypes u16 where

instance Impl_7 : Roots u16 where
  nth_root := fun (self : u16) (n : u32) => do (Impl_7.nth_root.go self n)
  sqrt := fun (self : u16) => do (Impl_7.sqrt.go self)
  cbrt := fun (self : u16) => do (Impl_7.cbrt.go self)

@[reducible] instance Impl_1.AssociatedTypes : Roots.AssociatedTypes i16 where

instance Impl_1 : Roots i16 where
  nth_root := fun (self : i16) (n : u32) => do
    if (← (self >=? (0 : i16))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          u16 (← (rust_primitives.hax.cast_op self : RustM u16)) n)) :
        RustM i16)
    else do
      let _ ← (hax_lib.assert (← (num_integer.Integer.is_odd u32 n)));
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          u16
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl_1.wrapping_neg self)) :
            RustM u16))
          n)) :
        RustM i16)))
  sqrt := fun (self : i16) => do
    let _ ← (hax_lib.assert (← (self >=? (0 : i16))));
    (rust_primitives.hax.cast_op
      (← (Roots.sqrt u16 (← (rust_primitives.hax.cast_op self : RustM u16)))) :
      RustM i16)
  cbrt := fun (self : i16) => do
    if (← (self >=? (0 : i16))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.cbrt u16 (← (rust_primitives.hax.cast_op self : RustM u16))))
        :
        RustM i16)
    else do
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.cbrt
          u16
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl_1.wrapping_neg self)) :
            RustM u16)))) :
        RustM i16)))

@[spec]
def Impl_10.sqrt.go (a : u128) : RustM u128 := do
  if (← ((← (bits u128 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if
    (← (a
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u64.MAX :
        RustM u128)))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.sqrt u64 (← (rust_primitives.hax.cast_op a : RustM u64)))) :
        RustM u128)
    else do
      let lo : u128 ←
        ((← (Roots.sqrt u128 (← (a >>>? (2 : u32))))) <<<? (1 : i32));
      let hi : u128 ← (lo +? (1 : u128));
      if (← ((← (hi *? hi)) <=? a)) then do (pure hi) else do (pure lo)
  else do
    if (← (a <? (4 : u128))) then do
      (rust_primitives.hax.cast_op (← (a >? (0 : u128))) : RustM u128)
    else do
      let next : (u128 -> RustM u128) :=
        (fun x => (do ((← ((← (a /? x)) +? x)) >>>? (1 : i32)) : RustM u128));
      (fixpoint u128 (u128 -> RustM u128) (← (Impl_10.sqrt.go.guess a)) next)

@[spec]
def Impl_10.nth_root.go (a : u128) (n : u32) : RustM u128 := do
  match n with
    | 0 => do
      let _ ←
        (rust_primitives.hax.never_to_any
          (← (core_models.panicking.panic "can\'t find a root of degree 0!")));
      if
      (← ((← ((← (bits u128 rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : u128) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u128))) : RustM u128)
      else do
        if
        (← ((← (bits u128 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then
        do
          if
          (← (a
            <=? (← (rust_primitives.hax.cast_op
              core_models.legacy_int_modules.u64.MAX :
              RustM u128)))) then do
            (rust_primitives.hax.cast_op
              (← (Roots.nth_root
                u64 (← (rust_primitives.hax.cast_op a : RustM u64)) n)) :
              RustM u128)
          else do
            let lo : u128 ←
              ((← (Roots.nth_root u128 (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : u128 ← (lo +? (1 : u128));
            if
            (← ((← ((← (core_models.num.Impl_10.trailing_zeros
                  (← (core_models.num.Impl_10.next_power_of_two hi))))
                *? n))
              >=? (← (bits u128 rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow u128
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_10.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (u128 -> RustM u128) :=
            (fun x =>
              (do
              let y : u128 ←
                match
                  (← (num_traits.pow.checked_pow u128
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : u128));
              ((← (y
                  +? (← (x
                    *? (← (rust_primitives.hax.cast_op n1 : RustM u128))))))
                /? (← (rust_primitives.hax.cast_op n : RustM u128))) :
              RustM u128));
          (fixpoint u128 (u128 -> RustM u128)
            (← (Impl_10.nth_root.go.guess a n))
            next)
    | 1 => do (pure a)
    | 2 => do (Roots.sqrt u128 a)
    | 3 => do (Roots.cbrt u128 a)
    | _ => do
      let _ := rust_primitives.hax.Tuple0.mk;
      if
      (← ((← ((← (bits u128 rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : u128) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u128))) : RustM u128)
      else do
        if
        (← ((← (bits u128 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then
        do
          if
          (← (a
            <=? (← (rust_primitives.hax.cast_op
              core_models.legacy_int_modules.u64.MAX :
              RustM u128)))) then do
            (rust_primitives.hax.cast_op
              (← (Roots.nth_root
                u64 (← (rust_primitives.hax.cast_op a : RustM u64)) n)) :
              RustM u128)
          else do
            let lo : u128 ←
              ((← (Roots.nth_root u128 (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : u128 ← (lo +? (1 : u128));
            if
            (← ((← ((← (core_models.num.Impl_10.trailing_zeros
                  (← (core_models.num.Impl_10.next_power_of_two hi))))
                *? n))
              >=? (← (bits u128 rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow u128
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_10.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (u128 -> RustM u128) :=
            (fun x =>
              (do
              let y : u128 ←
                match
                  (← (num_traits.pow.checked_pow u128
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : u128));
              ((← (y
                  +? (← (x
                    *? (← (rust_primitives.hax.cast_op n1 : RustM u128))))))
                /? (← (rust_primitives.hax.cast_op n : RustM u128))) :
              RustM u128));
          (fixpoint u128 (u128 -> RustM u128)
            (← (Impl_10.nth_root.go.guess a n))
            next)

@[spec]
def Impl_10.cbrt.go (a : u128) : RustM u128 := do
  if (← ((← (bits u128 rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if
    (← (a
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u64.MAX :
        RustM u128)))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.cbrt u64 (← (rust_primitives.hax.cast_op a : RustM u64)))) :
        RustM u128)
    else do
      let lo : u128 ←
        ((← (Roots.cbrt u128 (← (a >>>? (3 : u32))))) <<<? (1 : i32));
      let hi : u128 ← (lo +? (1 : u128));
      if (← ((← ((← (hi *? hi)) *? hi)) <=? a)) then do
        (pure hi)
      else do
        (pure lo)
  else do
    if
    (← ((← (bits u128 rust_primitives.hax.Tuple0.mk)) <=? (32 : u32))) then do
      let x : u128 := a;
      let y2 : u128 := (0 : u128);
      let y : u128 := (0 : u128);
      let smax : u32 ←
        ((← (bits u128 rust_primitives.hax.Tuple0.mk)) /? (3 : u32));
      let ⟨x, y, y2⟩ ←
        (core_models.iter.traits.iterator.Iterator.fold
          (← (core_models.iter.traits.collect.IntoIterator.into_iter
            (core_models.iter.adapters.rev.Rev
              (core_models.ops.range.Range u32))
            (← (core_models.iter.traits.iterator.Iterator.rev
              (core_models.ops.range.Range u32)
              (core_models.ops.range.Range.mk
                (start := (0 : u32))
                (_end := (← (smax +? (1 : u32)))))))))
          (rust_primitives.hax.Tuple3.mk x y y2)
          (fun ⟨x, y, y2⟩ s =>
            (do
            let s : u32 ← (s *? (3 : u32));
            let y2 : u128 ← (y2 *? (4 : u128));
            let y : u128 ← (y *? (2 : u128));
            let b : u128 ← ((← ((3 : u128) *? (← (y2 +? y)))) +? (1 : u128));
            if (← ((← (x >>>? s)) >=? b)) then do
              let x : u128 ← (x -? (← (b <<<? s)));
              let y2 : u128 ← (y2 +? (← ((← ((2 : u128) *? y)) +? (1 : u128))));
              let y : u128 ← (y +? (1 : u128));
              (pure (rust_primitives.hax.Tuple3.mk x y y2))
            else do
              (pure (rust_primitives.hax.Tuple3.mk x y y2)) :
            RustM (rust_primitives.hax.Tuple3 u128 u128 u128))));
      (pure y)
    else do
      if (← (a <? (8 : u128))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : u128))) : RustM u128)
      else do
        if
        (← (a
          <=? (← (rust_primitives.hax.cast_op
            core_models.legacy_int_modules.u32.MAX :
            RustM u128)))) then do
          (rust_primitives.hax.cast_op
            (← (Roots.cbrt u32 (← (rust_primitives.hax.cast_op a : RustM u32))))
            :
            RustM u128)
        else do
          let next : (u128 -> RustM u128) :=
            (fun x =>
              (do
              ((← ((← (a /? (← (x *? x)))) +? (← (x *? (2 : u128)))))
                /? (3 : u128)) :
              RustM u128));
          (fixpoint u128 (u128 -> RustM u128)
            (← (Impl_10.cbrt.go.guess a))
            next)

@[reducible] instance Impl_10.AssociatedTypes : Roots.AssociatedTypes u128 where

instance Impl_10 : Roots u128 where
  nth_root := fun (self : u128) (n : u32) => do (Impl_10.nth_root.go self n)
  sqrt := fun (self : u128) => do (Impl_10.sqrt.go self)
  cbrt := fun (self : u128) => do (Impl_10.cbrt.go self)

@[reducible] instance Impl_4.AssociatedTypes : Roots.AssociatedTypes i128 where

instance Impl_4 : Roots i128 where
  nth_root := fun (self : i128) (n : u32) => do
    if (← (self >=? (0 : i128))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          u128 (← (rust_primitives.hax.cast_op self : RustM u128)) n)) :
        RustM i128)
    else do
      let _ ← (hax_lib.assert (← (num_integer.Integer.is_odd u32 n)));
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          u128
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl_4.wrapping_neg self)) :
            RustM u128))
          n)) :
        RustM i128)))
  sqrt := fun (self : i128) => do
    let _ ← (hax_lib.assert (← (self >=? (0 : i128))));
    (rust_primitives.hax.cast_op
      (← (Roots.sqrt u128 (← (rust_primitives.hax.cast_op self : RustM u128))))
      :
      RustM i128)
  cbrt := fun (self : i128) => do
    if (← (self >=? (0 : i128))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.cbrt
          u128 (← (rust_primitives.hax.cast_op self : RustM u128)))) :
        RustM i128)
    else do
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.cbrt
          u128
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl_4.wrapping_neg self)) :
            RustM u128)))) :
        RustM i128)))

@[spec]
def Impl_11.sqrt.go (a : usize) : RustM usize := do
  if (← ((← (bits usize rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if
    (← (a
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u64.MAX :
        RustM usize)))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.sqrt u64 (← (rust_primitives.hax.cast_op a : RustM u64)))) :
        RustM usize)
    else do
      let lo : usize ←
        ((← (Roots.sqrt usize (← (a >>>? (2 : u32))))) <<<? (1 : i32));
      let hi : usize ← (lo +? (1 : usize));
      if (← ((← (hi *? hi)) <=? a)) then do (pure hi) else do (pure lo)
  else do
    if (← (a <? (4 : usize))) then do
      (rust_primitives.hax.cast_op (← (a >? (0 : usize))) : RustM usize)
    else do
      let next : (usize -> RustM usize) :=
        (fun x => (do ((← ((← (a /? x)) +? x)) >>>? (1 : i32)) : RustM usize));
      (fixpoint usize (usize -> RustM usize) (← (Impl_11.sqrt.go.guess a)) next)

@[spec]
def Impl_11.nth_root.go (a : usize) (n : u32) : RustM usize := do
  match n with
    | 0 => do
      let _ ←
        (rust_primitives.hax.never_to_any
          (← (core_models.panicking.panic "can\'t find a root of degree 0!")));
      if
      (← ((← ((← (bits usize rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : usize) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : usize))) : RustM usize)
      else do
        if
        (← ((← (bits usize rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then
        do
          if
          (← (a
            <=? (← (rust_primitives.hax.cast_op
              core_models.legacy_int_modules.u64.MAX :
              RustM usize)))) then do
            (rust_primitives.hax.cast_op
              (← (Roots.nth_root
                u64 (← (rust_primitives.hax.cast_op a : RustM u64)) n)) :
              RustM usize)
          else do
            let lo : usize ←
              ((← (Roots.nth_root usize (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : usize ← (lo +? (1 : usize));
            if
            (← ((← ((← (core_models.num.Impl_11.trailing_zeros
                  (← (core_models.num.Impl_11.next_power_of_two hi))))
                *? n))
              >=? (← (bits usize rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow usize
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_11.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (usize -> RustM usize) :=
            (fun x =>
              (do
              let y : usize ←
                match
                  (← (num_traits.pow.checked_pow usize
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : usize));
              ((← (y
                  +? (← (x
                    *? (← (rust_primitives.hax.cast_op n1 : RustM usize))))))
                /? (← (rust_primitives.hax.cast_op n : RustM usize))) :
              RustM usize));
          (fixpoint usize (usize -> RustM usize)
            (← (Impl_11.nth_root.go.guess a n))
            next)
    | 1 => do (pure a)
    | 2 => do (Roots.sqrt usize a)
    | 3 => do (Roots.cbrt usize a)
    | _ => do
      let _ := rust_primitives.hax.Tuple0.mk;
      if
      (← ((← ((← (bits usize rust_primitives.hax.Tuple0.mk)) <=? n))
        ||? (← (a <? (← ((1 : usize) <<<? n)))))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : usize))) : RustM usize)
      else do
        if
        (← ((← (bits usize rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then
        do
          if
          (← (a
            <=? (← (rust_primitives.hax.cast_op
              core_models.legacy_int_modules.u64.MAX :
              RustM usize)))) then do
            (rust_primitives.hax.cast_op
              (← (Roots.nth_root
                u64 (← (rust_primitives.hax.cast_op a : RustM u64)) n)) :
              RustM usize)
          else do
            let lo : usize ←
              ((← (Roots.nth_root usize (← (a >>>? n)) n)) <<<? (1 : i32));
            let hi : usize ← (lo +? (1 : usize));
            if
            (← ((← ((← (core_models.num.Impl_11.trailing_zeros
                  (← (core_models.num.Impl_11.next_power_of_two hi))))
                *? n))
              >=? (← (bits usize rust_primitives.hax.Tuple0.mk)))) then do
              match
                (← match
                  (← (num_traits.pow.checked_pow usize
                    hi
                    (← (rust_primitives.hax.cast_op n : RustM usize))))
                with
                  | (core_models.option.Option.Some  x) => do
                    match (← (x <=? a)) with
                      | true => do (pure (core_models.option.Option.Some hi))
                      | _ => do (pure core_models.option.Option.None)
                  | _ => do (pure core_models.option.Option.None))
              with
                | (core_models.option.Option.Some  x) => do (pure x)
                | (core_models.option.Option.None ) => do (pure lo)
            else do
              if (← ((← (core_models.num.Impl_11.pow hi n)) <=? a)) then do
                (pure hi)
              else do
                (pure lo)
        else do
          let n1 : u32 ← (n -? (1 : u32));
          let next : (usize -> RustM usize) :=
            (fun x =>
              (do
              let y : usize ←
                match
                  (← (num_traits.pow.checked_pow usize
                    x
                    (← (rust_primitives.hax.cast_op n1 : RustM usize))))
                with
                  | (core_models.option.Option.Some  ax) => do (a /? ax)
                  | (core_models.option.Option.None ) => do (pure (0 : usize));
              ((← (y
                  +? (← (x
                    *? (← (rust_primitives.hax.cast_op n1 : RustM usize))))))
                /? (← (rust_primitives.hax.cast_op n : RustM usize))) :
              RustM usize));
          (fixpoint usize (usize -> RustM usize)
            (← (Impl_11.nth_root.go.guess a n))
            next)

@[spec]
def Impl_11.cbrt.go (a : usize) : RustM usize := do
  if (← ((← (bits usize rust_primitives.hax.Tuple0.mk)) >? (64 : u32))) then do
    if
    (← (a
      <=? (← (rust_primitives.hax.cast_op
        core_models.legacy_int_modules.u64.MAX :
        RustM usize)))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.cbrt u64 (← (rust_primitives.hax.cast_op a : RustM u64)))) :
        RustM usize)
    else do
      let lo : usize ←
        ((← (Roots.cbrt usize (← (a >>>? (3 : u32))))) <<<? (1 : i32));
      let hi : usize ← (lo +? (1 : usize));
      if (← ((← ((← (hi *? hi)) *? hi)) <=? a)) then do
        (pure hi)
      else do
        (pure lo)
  else do
    if
    (← ((← (bits usize rust_primitives.hax.Tuple0.mk)) <=? (32 : u32))) then do
      let x : usize := a;
      let y2 : usize := (0 : usize);
      let y : usize := (0 : usize);
      let smax : u32 ←
        ((← (bits usize rust_primitives.hax.Tuple0.mk)) /? (3 : u32));
      let ⟨x, y, y2⟩ ←
        (core_models.iter.traits.iterator.Iterator.fold
          (← (core_models.iter.traits.collect.IntoIterator.into_iter
            (core_models.iter.adapters.rev.Rev
              (core_models.ops.range.Range u32))
            (← (core_models.iter.traits.iterator.Iterator.rev
              (core_models.ops.range.Range u32)
              (core_models.ops.range.Range.mk
                (start := (0 : u32))
                (_end := (← (smax +? (1 : u32)))))))))
          (rust_primitives.hax.Tuple3.mk x y y2)
          (fun ⟨x, y, y2⟩ s =>
            (do
            let s : u32 ← (s *? (3 : u32));
            let y2 : usize ← (y2 *? (4 : usize));
            let y : usize ← (y *? (2 : usize));
            let b : usize ← ((← ((3 : usize) *? (← (y2 +? y)))) +? (1 : usize));
            if (← ((← (x >>>? s)) >=? b)) then do
              let x : usize ← (x -? (← (b <<<? s)));
              let y2 : usize ←
                (y2 +? (← ((← ((2 : usize) *? y)) +? (1 : usize))));
              let y : usize ← (y +? (1 : usize));
              (pure (rust_primitives.hax.Tuple3.mk x y y2))
            else do
              (pure (rust_primitives.hax.Tuple3.mk x y y2)) :
            RustM (rust_primitives.hax.Tuple3 usize usize usize))));
      (pure y)
    else do
      if (← (a <? (8 : usize))) then do
        (rust_primitives.hax.cast_op (← (a >? (0 : usize))) : RustM usize)
      else do
        if
        (← (a
          <=? (← (rust_primitives.hax.cast_op
            core_models.legacy_int_modules.u32.MAX :
            RustM usize)))) then do
          (rust_primitives.hax.cast_op
            (← (Roots.cbrt u32 (← (rust_primitives.hax.cast_op a : RustM u32))))
            :
            RustM usize)
        else do
          let next : (usize -> RustM usize) :=
            (fun x =>
              (do
              ((← ((← (a /? (← (x *? x)))) +? (← (x *? (2 : usize)))))
                /? (3 : usize)) :
              RustM usize));
          (fixpoint usize (usize -> RustM usize)
            (← (Impl_11.cbrt.go.guess a))
            next)

@[reducible] instance Impl_11.AssociatedTypes :
  Roots.AssociatedTypes usize
  where

instance Impl_11 : Roots usize where
  nth_root := fun (self : usize) (n : u32) => do (Impl_11.nth_root.go self n)
  sqrt := fun (self : usize) => do (Impl_11.sqrt.go self)
  cbrt := fun (self : usize) => do (Impl_11.cbrt.go self)

@[reducible] instance Impl_5.AssociatedTypes : Roots.AssociatedTypes isize where

instance Impl_5 : Roots isize where
  nth_root := fun (self : isize) (n : u32) => do
    if (← (self >=? (0 : isize))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          usize (← (rust_primitives.hax.cast_op self : RustM usize)) n)) :
        RustM isize)
    else do
      let _ ← (hax_lib.assert (← (num_integer.Integer.is_odd u32 n)));
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.nth_root
          usize
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl_5.wrapping_neg self)) :
            RustM usize))
          n)) :
        RustM isize)))
  sqrt := fun (self : isize) => do
    let _ ← (hax_lib.assert (← (self >=? (0 : isize))));
    (rust_primitives.hax.cast_op
      (← (Roots.sqrt
        usize (← (rust_primitives.hax.cast_op self : RustM usize)))) :
      RustM isize)
  cbrt := fun (self : isize) => do
    if (← (self >=? (0 : isize))) then do
      (rust_primitives.hax.cast_op
        (← (Roots.cbrt
          usize (← (rust_primitives.hax.cast_op self : RustM usize)))) :
        RustM isize)
    else do
      (-? (← (rust_primitives.hax.cast_op
        (← (Roots.cbrt
          usize
          (← (rust_primitives.hax.cast_op
            (← (core_models.num.Impl_5.wrapping_neg self)) :
            RustM usize)))) :
        RustM isize)))

end num_integer.roots

