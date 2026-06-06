// unsupported: ad-hoc iterator combinator chains in the body — e.g.
// `xs.iter().sum::<u64>()`, `xs.iter().map(|x| x*2).sum()`,
// `xs.iter().filter(|x| **x > 0).count()`, `xs.iter().fold(0, |acc, x| ...)`.
// Each link extracts to a method on `core::slice::Iter` or
// `core::iter::adapters::*`, none of which the Hax Lean prelude models.
// `lake build` fails with:
//   error: Unknown identifier `core.iter.adapters.map.Map.fold`
//   error: Unknown identifier `core.slice.iter.Iter.sum`
//   (etc.)
//
// Mechanical fix: replace the chain with structural recursion that walks
// the slice by index. Per the project's recursion-preference rule, this is
// the preferred shape over a `while` loop — a single decreasing measure
// (`xs.len() - i`) and no mutable accumulator state.
//
// Sibling pattern `iter_fold_to_while_loop.rs` covers the narrower case
// where the iterator combinator sits inside a stdlib `Range::fold` call
// with capturing-closure helpers (separate prelude failure mode); this
// pattern is for the common ad-hoc iterator-chain case.

// before

pub fn sum(xs: &[u64]) -> u64 {
    xs.iter().sum()
}

// after

fn sum_from(xs: &[u64], i: usize) -> u64 {
    if i >= xs.len() {
        0
    } else {
        xs[i] + sum_from(xs, i + 1)
    }
}

pub fn sum(xs: &[u64]) -> u64 {
    sum_from(xs, 0)
}
