// unsupported: a `for x in &[T] { ... }` loop (or `for &x in xs` over a
// slice) desugars to `IntoIterator::into_iter` followed by an
// `Iterator::next` driven loop. Hax extracts this as a call to
// `core_models.iter.traits.iterator.Iterator.fold` over
// `core_models.iter.traits.collect.IntoIterator (RustSlice T)`, and the
// Hax Lean prelude does not model either. `lake build` fails with an
// `Unknown identifier` error pointing at the `Iterator.fold` / slice
// `IntoIterator` symbols.
//
// Sibling pattern `iter_chain_to_recursion.rs` covers the same root
// cause for ad-hoc iterator combinator chains (`xs.iter().sum()`,
// `xs.iter().fold(...)`, etc.). This pattern is the for-loop surface
// variant — a `for` statement with mutable accumulators in the body —
// and additionally demonstrates the multi-accumulator case (here:
// `(sum, product)` carried as a tuple through the recursion).
//
// Mechanical fix: lift the accumulator(s) into parameters of a private
// tail-recursive helper that walks the slice by index. The public
// function seeds the helper with the loop's initial accumulator values
// (the identity elements for the operations being folded, when those
// match the desired empty-input behavior). Decreasing measure is
// `xs.len() - i`. Do NOT apply when the loop body contains `break`,
// `continue`, early `return`, or order-sensitive side effects — those
// need a different shape (see `while_loop_early_return.rs`).

// before

pub fn sum_product(numbers: &[i64]) -> (i64, i64) {
    let mut sum: i64 = 0;
    let mut product: i64 = 1;
    for &n in numbers {
        sum += n;
        product *= n;
    }
    (sum, product)
}

// after

fn sum_product_at(numbers: &[i64], i: usize, sum: i64, product: i64) -> (i64, i64) {
    if i >= numbers.len() {
        (sum, product)
    } else {
        sum_product_at(numbers, i + 1, sum + numbers[i], product * numbers[i])
    }
}

pub fn sum_product(numbers: &[i64]) -> (i64, i64) {
    sum_product_at(numbers, 0, 0, 1)
}
