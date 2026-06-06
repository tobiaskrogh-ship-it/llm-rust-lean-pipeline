
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


namespace next_code_point_u8

--  Mask of the value bits of a continuation byte.
def CONT_MASK : u8 := (63 : u8)

--  Returns the initial codepoint accumulator for the first byte.
@[spec]
def utf8_first_byte (byte : u8) (width : u32) : RustM u32 := do
  (rust_primitives.hax.cast_op
    (← (byte &&&? (← ((127 : u8) >>>? width)))) :
    RustM u32)

--  Returns the value of `ch` updated with continuation byte `byte`.
@[spec]
def utf8_acc_cont_byte (ch : u32) (byte : u8) : RustM u32 := do
  ((← (ch <<<? (6 : i32)))
    |||? (← (rust_primitives.hax.cast_op
      (← (byte &&&? CONT_MASK)) :
      RustM u32)))

--  # Safety
-- 
--  `bytes` must produce a valid UTF-8-like (UTF-8 or WTF-8) string.
@[spec]
def next_code_point (bytes : (core_models.slice.iter.Iter u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      (core_models.slice.iter.Iter u8)
      (core_models.option.Option u32))
    := do
  let ⟨tmp0, out⟩ ←
    (core_models.iter.traits.iterator.Iterator.next
      (core_models.slice.iter.Iter u8) bytes);
  let bytes : (core_models.slice.iter.Iter u8) := tmp0;
  match out with
    | (core_models.option.Option.Some  x) => do
      if (← (x <? (128 : u8))) then do
        (pure (rust_primitives.hax.Tuple2.mk
          bytes
          (core_models.option.Option.Some
            (← (rust_primitives.hax.cast_op x : RustM u32)))))
      else do
        let init : u32 ← (utf8_first_byte x (2 : u32));
        let ⟨tmp0, out⟩ ←
          (core_models.iter.traits.iterator.Iterator.next
            (core_models.slice.iter.Iter u8) bytes);
        let bytes : (core_models.slice.iter.Iter u8) := tmp0;
        let y : u8 ← (core_models.option.Impl.unwrap_or u8 out (0 : u8));
        let ch : u32 ← (utf8_acc_cont_byte init y);
        let ⟨bytes, ch⟩ ←
          if (← (x >=? (224 : u8))) then do
            let ⟨tmp0, out⟩ ←
              (core_models.iter.traits.iterator.Iterator.next
                (core_models.slice.iter.Iter u8) bytes);
            let bytes : (core_models.slice.iter.Iter u8) := tmp0;
            let z : u8 ← (core_models.option.Impl.unwrap_or u8 out (0 : u8));
            let y_z : u32 ←
              (utf8_acc_cont_byte
                (← (rust_primitives.hax.cast_op
                  (← (y &&&? CONT_MASK)) :
                  RustM u32))
                z);
            let ch : u32 ← ((← (init <<<? (12 : i32))) |||? y_z);
            if (← (x >=? (240 : u8))) then do
              let ⟨tmp0, out⟩ ←
                (core_models.iter.traits.iterator.Iterator.next
                  (core_models.slice.iter.Iter u8) bytes);
              let bytes : (core_models.slice.iter.Iter u8) := tmp0;
              let w : u8 ← (core_models.option.Impl.unwrap_or u8 out (0 : u8));
              let ch : u32 ←
                ((← ((← (init &&&? (7 : u32))) <<<? (18 : i32)))
                  |||? (← (utf8_acc_cont_byte y_z w)));
              (pure (rust_primitives.hax.Tuple2.mk bytes ch))
            else do
              (pure (rust_primitives.hax.Tuple2.mk bytes ch))
          else do
            (pure (rust_primitives.hax.Tuple2.mk bytes ch));
        let hax_temp_output : (core_models.option.Option u32) :=
          (core_models.option.Option.Some ch);
        (pure (rust_primitives.hax.Tuple2.mk bytes hax_temp_output))
    | (core_models.option.Option.None ) => do
      (pure (rust_primitives.hax.Tuple2.mk
        bytes
        core_models.option.Option.None))

end next_code_point_u8

