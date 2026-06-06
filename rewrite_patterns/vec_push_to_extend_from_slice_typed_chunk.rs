// unsupported: building a `Vec<T>` element-by-element with `Vec::push`.
// `alloc.vec.Impl_1.push` is **not** defined in the Hax Lean prelude
// (`Hax/core_models/epilogue/alloc.lean`), so `lake build` fails with:
//   error: Unknown identifier 'alloc.vec.Impl_1.push'
//
// The prelude *does* model `alloc.vec.Impl.new` (Vec::new),
// `alloc.vec.Impl_1.len` (Vec::len), `alloc.vec.Impl_2.extend_from_slice`
// (Vec::extend_from_slice), and `alloc.slice.Impl.to_vec`. So a Vec can
// be built incrementally — by extending it with fixed-size chunks
// instead of pushing single elements. The natural rewrite has two
// independent gotchas; both must be addressed:
//
// (1) `for &x in slice { ... }` extracts to
//     `core_models.iter.traits.iterator.Iterator.fold` over
//     `core_models.iter.traits.collect.IntoIterator (RustSlice T)` —
//     neither is modeled in the Hax Lean prelude. Fix per
//     `iter_chain_to_recursion.rs`: convert to index-based tail recursion.
//     (Preferred over `while`-loop rewrite per the recursion-preference
//     rule.)
//
// (2) `acc.extend_from_slice(&[x])` (inline size-1/size-N array literal)
//     extracts to
//         rust_primitives.unsize (RustArray.ofVec #v[x])
//     The `RustArray α (n : usize)` size parameter `n` is left as a
//     metavariable. Without a constraint from the surrounding context
//     (`unsize`'s return type is `RustM (Seq α)`, which erases the
//     size), Lean cannot solve `USize64.toNat ?n = 1` and `lake build`
//     fails with:
//         error: Application type mismatch:
//           The argument #v[x] has type Vector i64 1
//           but is expected to have type Vector i64 (USize64.toNat ?m)
//
//     Routing the element through an extra function parameter does NOT
//     help — the metavariable is unresolved regardless of where `x`
//     comes from. The fix is to put the array in a **typed let binding**
//     so the size appears in the let's type ascription:
//         let chunk: [T; N] = [...];
//         acc.extend_from_slice(&chunk);
//     Hax extracts the let with the explicit type:
//         let chunk : (RustArray T N) := (RustArray.ofVec #v[...]);
//     Now `RustArray T N` has the size in the type and `unsize chunk`
//     can determine it cleanly.
//
// This was verified on the HumanEval-style `intersperse(numbers, delim)`
// task (a function building `Vec<i64>` of length `2n - 1` by alternating
// elements and delimiters): all three stages — `cargo test`, `cargo hax
// into lean`, `lake build` — pass after the rewrite below, and the
// resulting Lean uses `partial_fixpoint`, which the proof stage handles
// via `Nat.strongRecOn` on `numbers.len() - i`.

// before

pub fn intersperse(numbers: &[i64], delimiter: i64) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let mut first = true;
    for &n in numbers {
        if !first {
            result.push(delimiter);
        }
        result.push(n);
        first = false;
    }
    result
}

// after

fn intersperse_at(numbers: &[i64], delimiter: i64, i: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= numbers.len() {
        acc
    } else {
        let n = numbers[i];
        let mut acc = acc;
        if i == 0 {
            // Typed let — Hax emits the size in the type annotation
            // `RustArray i64 1`, so `unsize` can elaborate the size.
            let chunk: [i64; 1] = [n];
            acc.extend_from_slice(&chunk);
        } else {
            let chunk: [i64; 2] = [delimiter, n];
            acc.extend_from_slice(&chunk);
        }
        intersperse_at(numbers, delimiter, i + 1, acc)
    }
}

pub fn intersperse(numbers: &[i64], delimiter: i64) -> Vec<i64> {
    intersperse_at(numbers, delimiter, 0, Vec::new())
}
