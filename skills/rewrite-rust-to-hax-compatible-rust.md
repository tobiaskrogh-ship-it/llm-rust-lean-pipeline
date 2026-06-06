---
name: rewrite-rust-to-hax-compatible-rust
description: Rewrite Rust code until it is compatible with Hax AND the extracted Lean compiles AND the result is provable downstream.
---

## Goal

Rewrite the working crate's Rust source so that:

1. `cargo hax into lean` succeeds (extraction).
2. `lake build` in `proofs/lean/extraction/` succeeds (extracted Lean compiles).
3. The extracted Lean is *provable downstream* — extraction can succeed in shapes that block proof. See "Hax-degenerate patterns" below.

## Available tools

- Built-in `Read`, `Grep`, `Glob` for inspection — consult reference Rust sources in `proof_patterns/<name>/src/lib.rs` first; explore the Hax prelude only when references don't cover what you need
- `Bash` — flexible shell for ad-hoc inspection (`find`, `wc`, inline `python3 -c ...`) beyond what `Read`/`Grep`/`Glob` cover.
- `TodoWrite` — track each rewrite step as a checklist; mark off as `run_cargo_test` then `run_cargo_hax_into_lean` then `run_lake_build` clear each one.
- `Agent` / `Task` — spawn a sub-agent for broad surveys (e.g. *"survey rewrite patterns in `rewrite_patterns/*` that match this error class"*).
- `apply_file_patch_tool` for edits to existing files
- `write_working_file` for creating new files
- `run_cargo_test`, `run_cargo_hax_into_lean`, `run_lake_build`

## Rules

- **After every change, `run_cargo_test` before doing anything else.** Tests are the contract — never modify them. A change that breaks `cargo test` is invalid even if it makes Hax/lake build happy; revert and try a different rewrite. This check is non-negotiable: do not call `run_cargo_hax_into_lean` or `run_lake_build` on a state you haven't first re-tested.
- **When Hax or lake build fails, consult the "Known Hax-incompatibility patterns" archive in the prompt FIRST** (before reading the Hax prelude, before reading example sources, before trying anything). The archive is a list of `// unsupported: ...` headers followed by `// before` / `// after` rewrites that have already been proven to work. If any header's error matches the stderr you just got, apply that `// after` shape directly. Only investigate from scratch when no pattern matches.
- Consult reference example sources (paths in prompt) after the archive — they show how full prior crates were rewritten end-to-end.
- Use `run_cargo_hax_into_lean` to detect incompatible patterns; stderr is the signal.
- After extraction succeeds, `run_lake_build`. Hax can extract code referencing undefined symbols.
- After lake build succeeds, check for **Hax-degenerate patterns** (extraction succeeds but the extracted Lean is wrong — see below). Then review the source for **provability-affecting patterns** (extracted Lean is correct but the proof is harder than it needs to be — see below)
- **Specifically watch for short-circuit `&&` / `||` over a partial op (`-`, `/`, `%`, oversize shift, OOB indexing).** Hax's `do`-block extraction is eager — every `←` bind runs before the `&&?` / `||?` combinator, so the partial RHS is evaluated regardless of the guard. `cargo test` ✓, `cargo hax into lean` ✓, `lake build` ✓ — but the extracted Lean diverges (`RustM.fail`) on the guard-protected input, silently breaking downstream proofs. Rewrite the predicate as `if guard { … } else { … }` instead. Full description and worked examples in the "Short-circuit `&&` / `||` erasure over partial operations" subsection below.
- You may not exclude non-test code from Hax via attributes.
- Only change what Hax / `lake build` / Hax-degenerate-detection actually flags. No style cleanup.

The order on every iteration: edit → `run_cargo_test` → `run_cargo_hax_into_lean` → `run_lake_build`. Each step gates the next. If `run_cargo_test` fails, fix the test break before continuing.

The order when an error appears: **match against archive patterns first** → consult example sources → explore Hax prelude. Don't skip ahead; the archive is faster and more reliable than exploration for any pattern it covers.


## Inline unsupported library calls

If `lake build` fails with `unknown identifier 'core_models.num.Impl_2.abs'` or similar, rewrite the offending call inline using primitive Rust:

| Method | Inline replacement |
|---|---|
| `x.abs()` (signed) | `if x < 0 { -x } else { x }` (preserve `i32::MIN` panic if tests exercise it) |
| `x.pow(n)` | hand-rolled multiplication loop |
| `x.checked_*` / `x.wrapping_*` | bare `+` / `*` (Hax encodes overflow checks) |
| `iter().sum()` / `.fold(...)` / iterator chains | explicit `for` or `while` | l

If `lake build` fails for non-symbol reasons (Hax bug, Lean syntax error in the extracted file), flag it in the final output and stop. Do not edit `.lake/packages/`.


## Provability-affecting patterns
### Prefer tail recursion over `while` loops when feasible

Before applying the `while`-loop guidance below, check whether the loop can be rewritten as a tail-recursive function. **Recursion via `partial_fixpoint` admits substantially cleaner proofs than `while`-loop body-step Hoare triples.** The recursion pattern proves correctness by `Nat.strongRecOn` on the recursion measure plus standard `unfold`/`rw`/induction — well-supported tactics. The `while`-loop pattern proves correctness via `Spec.MonoLoopCombinator.while_loop` + a body-step Hoare triple chained through `Triple.bind` in the `Std.Do` library — intricate, sparsely documented, and the dominant source of proof-stage stagnation in batch runs.

Reference: [`proof_patterns/recursion_example`](../proof_patterns/recursion_example) (canonical pattern), [`proof_patterns/factorial_modified`](../proof_patterns/factorial_modified) and [`proof_patterns/sum_to_n_modified`](../proof_patterns/sum_to_n_modified) (real targets verified this way). See [`rewrite_patterns/while_loop_to_recursion.rs`](../rewrite_patterns/while_loop_to_recursion.rs) for the canonical before/after shape.

**Apply the rewrite when ALL hold:**

- The function consists of a single `while` loop with no `break`/`continue`.
- The loop state is a single accumulator (or a tuple) that's threaded through unchanged across iterations.
- The iteration count is bounded by a clearly-decreasing measure (a counter, a monotone quantity, etc.).
- Stack depth in practice stays under ~10⁵ iterations (Rust does not guarantee tail-call optimisation; ~10⁵ is a safe rule-of-thumb). Bit-walking loops like Stein GCD's outer subtract-and-strip (≤64 iterations on `u64`) are well within this; iterating over millions of bytes would not be.

**Do NOT rewrite when:**

- The loop has `break`/`continue` with branching exit conditions.
- The state involves mutable borrows or non-trivial control flow that recursion can't carry cleanly as function parameters.
- The iteration depth is unbounded or could be very large (data-dependent on user input, e.g. processing arbitrary-length input).
- The algorithm's correctness depends on side effects or an iteration order recursion would obscure.

**Rewrite shape:** lift the loop into a private tail-recursive helper that takes the loop state as parameters and returns the final value when the loop condition becomes false; the public function just calls the helper with initial values. See the rewrite_patterns entry above for a minimal worked example.

When the rewrite is not feasible (or when applying it would break tests), fall back to the `while`-loop strategy described below.

### `while` loops

Do not add hax-lib annotations to `while` loops (no `#[hax_lib::requires(...)]`, no `loop_invariant!`, no `loop_decreases!`). The proof stage handles invariants and termination on the Lean side via `Spec.MonoLoopCombinator.while_loop`. Reference: [`proof_patterns/while_example`](../proof_patterns/while_example) — closed-proof example with the minimal Rust shape:

```rust
pub fn modulo_via_subtraction(a: u64, b: u64) -> u64 {
    let mut x = a;
    while x >= b {
        x -= b;
    }
    x
}
```

Five lines, no annotations. The natural loop invariant for such functions typically mentions partial u64 arithmetic (`%`, `/`, multiplication-with-overflow), which Hax's `pureP` / `grind` synthesis cannot lift to a pure `Prop`, so any annotation-based strategy fails at extraction anyway.

### Recursive functions and `partial_fixpoint`

Hax extracts recursive functions as `partial_fixpoint`. Reference: [`proof_patterns/recursion_example`](../proof_patterns/recursion_example) — closed-proof example demonstrating `Nat.strongRecOn`-based induction on `n.toNat` to discharge a `partial_fixpoint`-extracted recursion in Lean.

The Rust source again should be **minimal** — no precondition annotations, no decreases hints — when the proof stage will handle everything in Lean:

```rust
pub fn count_down(n: u64) -> u64 {
    if n == 0 { 0 } else { count_down(n - 1) }
}
```

If the function name collides with a Lean keyword (`partial_fixpoint`, `decreases`, `termination`, etc.), rename the crate's package — the extracted namespace inherits the package name, and the collision will produce a parse error in the extracted Lean.

### Detection

Before extraction (source-side):

```bash
# Short-circuit && / || over a partial op — silently eager in Hax extraction,
# breaks downstream proofs. Manual review needed; heuristic is noisy.
grep -nE '&&[^&]*[ (]([a-zA-Z_][a-zA-Z0-9_]*\s*[-/%]|[0-9]+\s*<<)' src/lib.rs
grep -nE '\|\|[^|]*[ (]([a-zA-Z_][a-zA-Z0-9_]*\s*[-/%]|[0-9]+\s*<<)' src/lib.rs
```

After extraction, before lake build:

```bash
# Crate-name / keyword collision in extracted file
lake build 2>&1 | grep "unexpected token 'partial_fixpoint'"
```


## Hax-degenerate patterns (extraction succeeds but proof is blocked)
### Short-circuit `&&` / `||` erasure over partial operations

Rust short-circuits `&&` and `||`: in `guard && rhs`, `rhs` is not evaluated when `guard` is false. **Hax's `do`-block extraction is eager** — every `←` bind runs before the `&&?` / `||?` combinator, so `rhs` is evaluated regardless. If `rhs` contains a partial op that's *only safe under the guard* (a `-`/`/`/`%` near zero, an oversize shift, an indexing op past the end, …), the extracted Lean diverges (`RustM.fail`) on inputs the Rust function handles by short-circuit.

**Symptom: extraction and `lake build` both pass cleanly — no error, no warning.** The divergence only surfaces in the proof stage as obligations that are false in the extracted model, typically at the `n = 0` or boundary instance. The proof agent then either leaves `sorry` with a "model diverges" admission or has to scaffold around `RustM.fail` witnesses. Several alloc benchmarks (`is_size_align_valid_usize`, `repeat_packed_usize`, `repeat_usize`) hit this exactly.

Common offenders — every one of these is FALSE-in-model under the naïve `&&` rewrite:

| Rust source (looks safe) | Extracted-Lean behavior at the guard-protected input |
|---|---|
| `n != 0 && (n & (n - 1)) == 0` | `n - 1` evaluated at `n = 0` → `RustM.fail .integerOverflow` |
| `b != 0 && a / b > c` | `a / b` evaluated at `b = 0` → `RustM.fail .divisionByZero` |
| `i < len && arr[i] == x` | `arr[i]` evaluated at `i >= len` → `RustM.fail` (OOB) |
| `s < 64 && (1u64 << s) != 0` | `1 << s` evaluated at `s >= 64` → `RustM.fail` (oversize shift) |

**Fix: rewrite to `if`/`else`.** Hax preserves `if` short-circuiting — the else branch is gated by the guard's value, so the partial op stays under its guard through extraction. Rust semantics are byte-identical:

```rust
// before — extracts `(← guard) &&? (← partial_op)`, eager
n != 0 && (n & (n - 1)) == 0

// after — extracts `if guard then a else b`, partial op stays under the guard
if n == 0 { false } else { (n & (n - 1)) == 0 }
```

The same rule applies to `||` with a partial RHS — rewrite to `if guard { true } else { rhs }`.

Reference: [`rewrite_patterns/short_circuit_and_with_partial_op.rs`](../rewrite_patterns/short_circuit_and_with_partial_op.rs) (general rule) and [`rewrite_patterns/int_is_power_of_two_method.rs`](../rewrite_patterns/int_is_power_of_two_method.rs) (the concrete power-of-two case).



## Final output

- The Hax / `lake build` errors that drove each change
- Library calls inlined and their replacements
- Patterns considered but not changed
- Any change suspected of altering semantics (and why tests still cover it)
- Hax-degenerate patterns that you couldn't fix at the source level (so the proof stage can plan)
