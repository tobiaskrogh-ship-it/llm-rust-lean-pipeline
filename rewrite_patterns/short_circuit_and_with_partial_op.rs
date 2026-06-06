// unsupported: `&&` (or `||`) short-circuit where the right-hand operand
// contains a *partial* operation on usize/u64/i64 (`-`, `/`, `%`, an
// out-of-range shift, an indexing op past the slice end, etc.). In Rust
// the partial op is never evaluated when the guard makes it unsafe —
// `&&` and `||` short-circuit. Hax's `do`-block extraction is **eager**:
// every `←` bind runs *before* the `&&?` / `||?` combinator, so the
// partial op is evaluated unconditionally and the extracted Lean
// function diverges (`RustM.fail Error.integerOverflow`,
// `Error.divisionByZero`, or similar) on the inputs the Rust function
// handles by short-circuit.
//
// Symptom: `cargo test`, `cargo hax into lean`, and `lake build` all
// pass cleanly — no error, no warning. The divergence only surfaces in
// the proof stage: obligations that quantify over the guard-protected
// input (typically the `n = 0` or boundary instance) become FALSE in
// the extracted model. The proof agent either leaves `sorry`s with
// "model diverges" admissions or has to scaffold around `RustM.fail`
// witnesses, neither of which is its job.
//
// Workaround: rewrite to an explicit `if`/`else`. Hax DOES preserve
// `if` short-circuiting — the else branch is gated by the guard's
// value, so the partial op stays under its guard through extraction.
// The Rust semantics are byte-identical.
//
// Common offenders (all are FALSE-in-model under the naïve rewrite):
//   - `n != 0 && (n & (n - 1)) == 0`         // n-1 underflow at n=0
//   - `b != 0 && a / b > c`                  // div by zero at b=0
//   - `b != 0 && a % b == r`                 // mod by zero at b=0
//   - `i < len && arr[i] == x`               // OOB index at i>=len
//   - `s != 0 && (1u64 << s) & m != 0`       // oversize shift at s>=64
//
// The same rule applies to `||` with a partial RHS — rewrite to
// `if guard { true } else { rhs }`.
//
// Sibling pattern `int_is_power_of_two_method.rs` is the concrete
// power-of-two case that drove this entry.

// before

fn is_power_of_two_usize(n: usize) -> bool {
    // Looks safe in Rust (`n - 1` is guarded by `n != 0`), but the
    // extracted Lean evaluates `n -? 1` unconditionally and panics
    // (`RustM.fail Error.integerOverflow`) at `n = 0`.
    n != 0 && (n & (n - 1)) == 0
}

// after

fn is_power_of_two_usize(n: usize) -> bool {
    // `if`/`else` survives Hax extraction with the guard intact:
    // the else branch (and its `n - 1`) is only evaluated when n != 0.
    if n == 0 { false } else { (n & (n - 1)) == 0 }
}
