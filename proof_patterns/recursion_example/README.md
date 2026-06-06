# recursion_example — canonical proof pattern for `partial_fixpoint`-extracted targets

Closed-proof demonstration of how to verify a Hax-extracted function that recurses. If the proof generator selected this example, the target is recursive and likely follows the same pattern — read this file before attempting tactics.

## When this pattern applies

When the function recurses, Hax extracts it with the `partial_fixpoint` keyword (visible in the extracted Lean as `def f := body partial_fixpoint`). The rewrite stage cannot encode recursion termination on the Rust side, so the proof obligation is to show termination + correctness Lean-side via strong induction on a Nat measure.

## Proof outline

1. **Strong induction on a Nat-valued measure of the input** via `Nat.strongRecOn generalizing <fn input>`. The measure is typically `n.toNat` for a single u64 input, or `m.toNat + n.toNat` for two inputs (e.g. gcd's iterative form needs the latter).
2. **`unfold <crate>.<fn>`** to expose the recursion's body.
3. **`by_cases` on the recursive guard** (often `n = 0` or `n.toNat = 0`).
4. **Base case**: substitute, the body reduces to a literal value; close with `rfl` or `simp`.
5. **Step case**: discharge the partial-op preconditions (`n -? 1 = pure (n - 1)` via no-underflow proofs, `b ==? 0 = pure false` via `decide_eq_false`), then apply the IH with the strict-decrease witness on the chosen measure.

## Reusable shape

```lean
induction h : <input>.toNat using Nat.strongRecOn generalizing <input> with
| _ k ih =>
  unfold <crate>.<fn>
  by_cases h0 : <input>.toNat = 0
  · -- base: input is 0
    have : <input> = 0 := UInt64.toNat_inj.mp (by simp [h0])
    subst this; rfl
  · -- step: reduce ==?, -?, etc. then apply IH
    ...
    apply ih (<recursive arg>).toNat
    · -- prove (recursive arg).toNat < k
      ...
    · rfl
```

If the function takes multiple arguments and the natural measure is e.g. `m.toNat + n.toNat`, switch the induction predicate accordingly:

```lean
induction h : (m.toNat + n.toNat) using Nat.strongRecOn generalizing m n
```
