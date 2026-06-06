
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


namespace chacha20.hacspec_helper

@[spec]
def to_le_u32s_3 (bytes : (RustSlice u8)) : RustM (RustArray u32 3) := do
  let out : (RustArray u32 3) ←
    (rust_primitives.hax.repeat (0 : u32) (3 : usize));
  let out : (RustArray u32 3) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (3 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        (rust_primitives.hax.monomorphized_update_at.update_at_usize
          out
          i
          (← (core_models.num.Impl_8.from_le_bytes
            (← (core_models.result.Impl.unwrap
              (RustArray u8 4)
              core_models.array.TryFromSliceError
              (← (core_models.convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 4)
                (← bytes[
                  (core_models.ops.range.Range.mk
                    (start := (← ((4 : usize) *? i)))
                    (_end := (← ((← ((4 : usize) *? i)) +? (4 : usize)))))
                  ]_?)))))))) :
        RustM (RustArray u32 3))));
  (pure out)

@[spec]
def to_le_u32s_8 (bytes : (RustSlice u8)) : RustM (RustArray u32 8) := do
  let out : (RustArray u32 8) ←
    (rust_primitives.hax.repeat (0 : u32) (8 : usize));
  let out : (RustArray u32 8) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        (rust_primitives.hax.monomorphized_update_at.update_at_usize
          out
          i
          (← (core_models.num.Impl_8.from_le_bytes
            (← (core_models.result.Impl.unwrap
              (RustArray u8 4)
              core_models.array.TryFromSliceError
              (← (core_models.convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 4)
                (← bytes[
                  (core_models.ops.range.Range.mk
                    (start := (← ((4 : usize) *? i)))
                    (_end := (← ((← ((4 : usize) *? i)) +? (4 : usize)))))
                  ]_?)))))))) :
        RustM (RustArray u32 8))));
  (pure out)

@[spec]
def to_le_u32s_16 (bytes : (RustSlice u8)) : RustM (RustArray u32 16) := do
  let out : (RustArray u32 16) ←
    (rust_primitives.hax.repeat (0 : u32) (16 : usize));
  let out : (RustArray u32 16) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        (rust_primitives.hax.monomorphized_update_at.update_at_usize
          out
          i
          (← (core_models.num.Impl_8.from_le_bytes
            (← (core_models.result.Impl.unwrap
              (RustArray u8 4)
              core_models.array.TryFromSliceError
              (← (core_models.convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 4)
                (← bytes[
                  (core_models.ops.range.Range.mk
                    (start := (← ((4 : usize) *? i)))
                    (_end := (← ((← ((4 : usize) *? i)) +? (4 : usize)))))
                  ]_?)))))))) :
        RustM (RustArray u32 16))));
  (pure out)

@[spec]
def u32s_to_le_bytes (state : (RustArray u32 16)) :
    RustM (RustArray u8 64) := do
  let out : (RustArray u8 64) ←
    (rust_primitives.hax.repeat (0 : u8) (64 : usize));
  let out : (RustArray u8 64) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (core_models.slice.Impl.len u32 (← (rust_primitives.unsize state))))
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        let tmp : (RustArray u8 4) ←
          (core_models.num.Impl_8.to_le_bytes (← state[i]_?));
        (rust_primitives.hax.folds.fold_range
          (0 : usize)
          (4 : usize)
          (fun out _ => (do (pure true) : RustM Bool))
          out
          (fun out j =>
            (do
            (rust_primitives.hax.monomorphized_update_at.update_at_usize
              out
              (← ((← (i *? (4 : usize))) +? j))
              (← tmp[j]_?)) :
            RustM (RustArray u8 64)))) :
        RustM (RustArray u8 64))));
  (pure out)

@[spec]
def xor_state (state : (RustArray u32 16)) (other : (RustArray u32 16)) :
    RustM (RustArray u32 16) := do
  let state : (RustArray u32 16) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        (rust_primitives.hax.monomorphized_update_at.update_at_usize
          state
          i
          (← ((← state[i]_?) ^^^? (← other[i]_?)))) :
        RustM (RustArray u32 16))));
  (pure state)

@[spec]
def add_state (state : (RustArray u32 16)) (other : (RustArray u32 16)) :
    RustM (RustArray u32 16) := do
  let state : (RustArray u32 16) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        (rust_primitives.hax.monomorphized_update_at.update_at_usize
          state
          i
          (← (core_models.num.Impl_8.wrapping_add
            (← state[i]_?)
            (← other[i]_?)))) :
        RustM (RustArray u32 16))));
  (pure state)

@[spec]
def update_array (array : (RustArray u8 64)) (val : (RustSlice u8)) :
    RustM (RustArray u8 64) := do
  let _ ←
    (hax_lib.assert
      (← ((64 : usize) >=? (← (core_models.slice.Impl.len u8 val)))));
  let array : (RustArray u8 64) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (core_models.slice.Impl.len u8 val))
      (fun array _ => (do (pure true) : RustM Bool))
      array
      (fun array i =>
        (do
        (rust_primitives.hax.monomorphized_update_at.update_at_usize
          array
          i
          (← val[i]_?)) :
        RustM (RustArray u8 64))));
  (pure array)

end chacha20.hacspec_helper


namespace chacha20

abbrev State : Type := (RustArray u32 16)

abbrev Block : Type := (RustArray u8 64)

abbrev ChaChaIV : Type := (RustArray u8 12)

abbrev ChaChaKey : Type := (RustArray u8 32)

@[spec]
def chacha20_line
    (a : usize)
    (b : usize)
    (d : usize)
    (s : u32)
    (m : (RustArray u32 16)) :
    RustM (RustArray u32 16) := do
  let state : (RustArray u32 16) := m;
  let state : (RustArray u32 16) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      state
      a
      (← (core_models.num.Impl_8.wrapping_add (← state[a]_?) (← state[b]_?))));
  let state : (RustArray u32 16) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      state
      d
      (← ((← state[d]_?) ^^^? (← state[a]_?))));
  let state : (RustArray u32 16) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      state
      d
      (← (core_models.num.Impl_8.rotate_left (← state[d]_?) s)));
  (pure state)

--  Quarter round operating on four state words. Caller must pass a, b, c, d < 16.
@[spec]
def chacha20_quarter_round
    (a : usize)
    (b : usize)
    (c : usize)
    (d : usize)
    (state : (RustArray u32 16)) :
    RustM (RustArray u32 16) := do
  let state : (RustArray u32 16) ← (chacha20_line a b d (16 : u32) state);
  let state : (RustArray u32 16) ← (chacha20_line c d b (12 : u32) state);
  let state : (RustArray u32 16) ← (chacha20_line a b d (8 : u32) state);
  (chacha20_line c d b (7 : u32) state)

@[spec]
def chacha20_double_round (state : (RustArray u32 16)) :
    RustM (RustArray u32 16) := do
  let state : (RustArray u32 16) ←
    (chacha20_quarter_round
      (0 : usize)
      (4 : usize)
      (8 : usize)
      (12 : usize)
      state);
  let state : (RustArray u32 16) ←
    (chacha20_quarter_round
      (1 : usize)
      (5 : usize)
      (9 : usize)
      (13 : usize)
      state);
  let state : (RustArray u32 16) ←
    (chacha20_quarter_round
      (2 : usize)
      (6 : usize)
      (10 : usize)
      (14 : usize)
      state);
  let state : (RustArray u32 16) ←
    (chacha20_quarter_round
      (3 : usize)
      (7 : usize)
      (11 : usize)
      (15 : usize)
      state);
  let state : (RustArray u32 16) ←
    (chacha20_quarter_round
      (0 : usize)
      (5 : usize)
      (10 : usize)
      (15 : usize)
      state);
  let state : (RustArray u32 16) ←
    (chacha20_quarter_round
      (1 : usize)
      (6 : usize)
      (11 : usize)
      (12 : usize)
      state);
  let state : (RustArray u32 16) ←
    (chacha20_quarter_round
      (2 : usize)
      (7 : usize)
      (8 : usize)
      (13 : usize)
      state);
  (chacha20_quarter_round
    (3 : usize)
    (4 : usize)
    (9 : usize)
    (14 : usize)
    state)

@[spec]
def chacha20_init
    (key : (RustArray u8 32))
    (iv : (RustArray u8 12))
    (ctr : u32) :
    RustM (RustArray u32 16) := do
  let key_u32 : (RustArray u32 8) ←
    (chacha20.hacspec_helper.to_le_u32s_8 (← (rust_primitives.unsize key)));
  let iv_u32 : (RustArray u32 3) ←
    (chacha20.hacspec_helper.to_le_u32s_3 (← (rust_primitives.unsize iv)));
  (pure (RustArray.ofVec #v[(1634760805 : u32),
                              (857760878 : u32),
                              (2036477234 : u32),
                              (1797285236 : u32),
                              (← key_u32[(0 : usize)]_?),
                              (← key_u32[(1 : usize)]_?),
                              (← key_u32[(2 : usize)]_?),
                              (← key_u32[(3 : usize)]_?),
                              (← key_u32[(4 : usize)]_?),
                              (← key_u32[(5 : usize)]_?),
                              (← key_u32[(6 : usize)]_?),
                              (← key_u32[(7 : usize)]_?),
                              ctr,
                              (← iv_u32[(0 : usize)]_?),
                              (← iv_u32[(1 : usize)]_?),
                              (← iv_u32[(2 : usize)]_?)]))

@[spec]
def chacha20_rounds_at (state : (RustArray u32 16)) (i : u32) :
    RustM (RustArray u32 16) := do
  if (← (i >=? (10 : u32))) then do
    (pure state)
  else do
    (chacha20_rounds_at (← (chacha20_double_round state)) (← (i +? (1 : u32))))
partial_fixpoint

@[spec]
def chacha20_rounds (state : (RustArray u32 16)) :
    RustM (RustArray u32 16) := do
  (chacha20_rounds_at state (0 : u32))

@[spec]
def chacha20_core (ctr : u32) (st0 : (RustArray u32 16)) :
    RustM (RustArray u32 16) := do
  let state : (RustArray u32 16) := st0;
  let state : (RustArray u32 16) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      state
      (12 : usize)
      (← (core_models.num.Impl_8.wrapping_add (← state[(12 : usize)]_?) ctr)));
  let k : (RustArray u32 16) ← (chacha20_rounds state);
  (chacha20.hacspec_helper.add_state state k)

@[spec]
def chacha20_key_block (state : (RustArray u32 16)) :
    RustM (RustArray u8 64) := do
  let state : (RustArray u32 16) ← (chacha20_core (0 : u32) state);
  (chacha20.hacspec_helper.u32s_to_le_bytes state)

@[spec]
def chacha20_key_block0 (key : (RustArray u8 32)) (iv : (RustArray u8 12)) :
    RustM (RustArray u8 64) := do
  let state : (RustArray u32 16) ← (chacha20_init key iv (0 : u32));
  (chacha20_key_block state)

@[spec]
def chacha20_encrypt_block
    (st0 : (RustArray u32 16))
    (ctr : u32)
    (plain : (RustArray u8 64)) :
    RustM (RustArray u8 64) := do
  let st : (RustArray u32 16) ← (chacha20_core ctr st0);
  let pl : (RustArray u32 16) ←
    (chacha20.hacspec_helper.to_le_u32s_16 (← (rust_primitives.unsize plain)));
  let encrypted : (RustArray u32 16) ←
    (chacha20.hacspec_helper.xor_state st pl);
  (chacha20.hacspec_helper.u32s_to_le_bytes encrypted)

--  Encrypt a partial final block. Caller must pass plain.len() <= 64.
@[spec]
def chacha20_encrypt_last
    (st0 : (RustArray u32 16))
    (ctr : u32)
    (plain : (RustSlice u8)) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  let b : (RustArray u8 64) ←
    (rust_primitives.hax.repeat (0 : u8) (64 : usize));
  let b : (RustArray u8 64) ← (chacha20.hacspec_helper.update_array b plain);
  let b : (RustArray u8 64) ← (chacha20_encrypt_block st0 ctr b);
  (alloc.slice.Impl.to_vec u8
    (← b[
      (core_models.ops.range.Range.mk
        (start := (0 : usize))
        (_end := (← (core_models.slice.Impl.len u8 plain))))
      ]_?))

@[spec]
def chacha20_update_blocks
    (st0 : (RustArray u32 16))
    (m : (RustSlice u8))
    (i : usize)
    (num_blocks : usize)
    (acc : (alloc.vec.Vec u8 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  if (← (i >=? num_blocks)) then do
    (pure acc)
  else do
    let block : (RustArray u8 64) ←
      (core_models.result.Impl.unwrap
        (RustArray u8 64)
        core_models.array.TryFromSliceError
        (← (core_models.convert.TryInto.try_into
          (RustSlice u8)
          (RustArray u8 64)
          (← m[
            (core_models.ops.range.Range.mk
              (start := (← ((64 : usize) *? i)))
              (_end := (← ((← ((64 : usize) *? i)) +? (64 : usize)))))
            ]_?))));
    let b : (RustArray u8 64) ←
      (chacha20_encrypt_block
        st0
        (← (rust_primitives.hax.cast_op i : RustM u32))
        block);
    let acc : (alloc.vec.Vec u8 alloc.alloc.Global) := acc;
    let acc : (alloc.vec.Vec u8 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize b)));
    (chacha20_update_blocks st0 m (← (i +? (1 : usize))) num_blocks acc)
partial_fixpoint

@[spec]
def chacha20_update (st0 : (RustArray u32 16)) (m : (RustSlice u8)) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  let num_blocks : usize ←
    ((← (core_models.slice.Impl.len u8 m)) /? (64 : usize));
  let remainder_len : usize ←
    ((← (core_models.slice.Impl.len u8 m)) %? (64 : usize));
  let blocks_out : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (chacha20_update_blocks
      st0
      m
      (0 : usize)
      num_blocks
      (← (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk)));
  let blocks_out : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    if (← (remainder_len !=? (0 : usize))) then do
      let b : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (chacha20_encrypt_last
          st0
          (← (rust_primitives.hax.cast_op num_blocks : RustM u32))
          (← m[
            (core_models.ops.range.Range.mk
              (start := (← ((64 : usize) *? num_blocks)))
              (_end := (← (core_models.slice.Impl.len u8 m))))
            ]_?));
      let blocks_out : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global
          blocks_out
          (← (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec u8 alloc.alloc.Global) b)));
      (pure blocks_out)
    else do
      (pure blocks_out);
  (pure blocks_out)

@[spec]
def chacha20
    (m : (RustSlice u8))
    (key : (RustArray u8 32))
    (iv : (RustArray u8 12))
    (ctr : u32) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  let state : (RustArray u32 16) ← (chacha20_init key iv ctr);
  (chacha20_update state m)

end chacha20

