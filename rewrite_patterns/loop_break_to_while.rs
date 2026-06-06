// unsupported: `loop { if cond { break; } ... }` (a Rust infinite `loop`
// with an internal early `break` guarding the exit). Hax extraction does
// not lower this shape into the `rust_primitives.hax.while_loop` combinator;
// instead it emits a placeholder
//   `let ⟨...⟩ := sorry;`
// for the loop's mutated-state tuple, which `lake build` rejects with
// `Invalid '⟨...⟩' notation: The expected type of this term could not be
// determined`.
// Workaround: rewrite as an explicit `while` loop with the negated exit
// condition. Hax extracts `while` loops into the supported combinator.

// before

let mut r: u64 = 1;
let mut d: u64 = 1;
loop {
    if d > k {
        break;
    }
    r = multiply_and_divide(r, n, d);
    n = n - 1;
    d = d + 1;
}
r

// after

let mut r: u64 = 1;
let mut d: u64 = 1;
while d <= k {
    r = multiply_and_divide(r, n, d);
    n = n - 1;
    d = d + 1;
}
r
