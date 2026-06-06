// unsupported: `loop_invariant!` whose predicate uses a partial operation
// on u64 (`%`, `/`, `+`, `-`, `*`). The predicate extracts to RustM-typed
// values; the macro's `pureP/grind` synthesis can't lift them to a pure
// Prop (even with a `requires(b > 0)` precondition — synthesis runs at
// macro expansion time, before preconditions are in scope). `lake build`
// fails on `failed to synthesize default value for parameter 'pureInv'`.

// before

#[hax_lib::requires(b > 0)]
pub fn modulo_via_subtraction(a: u64, b: u64) -> u64 {
    let mut x = a;
    while x >= b {
        hax_lib::loop_invariant!(x % b == a % b);
        hax_lib::loop_decreases!(x);
        x -= b;
    }
    x
}

// after

pub fn modulo_via_subtraction(a: u64, b: u64) -> u64 {
    let mut x = a;
    while x >= b {
        x -= b;
    }
    x
}
