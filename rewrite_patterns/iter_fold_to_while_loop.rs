// unsupported: calling `Range::fold` (or any iterator-combinator method
// whose bound is `FnMut(Acc, Self::Item) -> Acc`), and helpers that
// *return* `impl FnMut(...) -> T`. Both are flagged by Hax as
//   error: [HAX0001] Unsupported equality constraints on associated
//   types of parent trait
// (https://github.com/hacspec/hax/issues/1923) — the `FnOnce::Output = Acc`
// equality on `FnMut`'s parent trait is what the Lean printer rejects.
//
// The sibling pattern `assoc_type_equality_on_parent.rs` covers the
// straightforward fix (replace an `impl Fn*(X) -> Y` *parameter* bound
// with a `fn(X) -> Y` pointer). That fix does NOT work when:
//   (a) the offending bound sits on a stdlib method like `Range::fold`
//       (we can't change the stdlib signature), or
//   (b) a helper returns `impl FnMut(...)` while capturing its inputs
//       (a capturing closure cannot be coerced to a `fn(...)` pointer).
//
// Mechanical fix: drop the helper and inline `Range::fold` as a `while`
// loop iterating `start..end` by hand. Non-capturing closure parameters
// are still converted to `fn(...)` pointers per the sibling pattern.

// before

use core::ops::Range;

pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

fn map_fold(
    mut f: impl FnMut(u64) -> u64,
    mut g: impl FnMut(u64, u64) -> u64,
) -> impl FnMut(u64, u64) -> u64 {
    move |acc, elt| g(acc, f(elt))
}

impl Map {
    pub fn fold(self, init: u64, g: impl FnMut(u64, u64) -> u64) -> u64 {
        self.iter.fold(init, map_fold(self.f, g))
    }
}

// after

use core::ops::Range;

pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

impl Map {
    pub fn fold(self, init: u64, g: fn(u64, u64) -> u64) -> u64 {
        let mut acc = init;
        let mut i = self.iter.start;
        let end = self.iter.end;
        while i < end {
            acc = g(acc, (self.f)(i));
            i = i + 1;
        }
        acc
    }
}
