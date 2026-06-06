-- Companion obligations file for the `gcd_while` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_while

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_whileObligations

/-!
## Proof status

The Rust source uses a `while`-loop, which Hax extracts via the
`rust_primitives.hax.while_loop` combinator. The combinator takes a
*termination expression* — Hax took the user-unspecified default and
extracted it as the constant `(rust_primitives.hax.int.from_machine
(0 : u32))`, i.e. the constant `0` regardless of the loop state.

This breaks the standard `rust_primitives.hax.while_loop.spec` lemma: its
hypothesis `pureTermination.val b' < pureTermination.val b` reduces to
`0 < 0`, which is unprovable. None of the five reference examples we
were given (`sum_to_n`, `factorial`, `saturating_sub`, `min`,
`add_one`) uses a `while_loop`, so there is no transferable proof
template for routing around this. Closing the loop-based postconditions
would require either:

  * descending from `rust_primitives.hax.while_loop` to its underlying
    `Loop.MonoLoopCombinator.while_loop` and applying
    `Spec.MonoLoopCombinator.while_loop` from
    `Hax.MissingLean.Std.Do.Triple.SpecLemmas` with a hand-written
    termination measure such as `fun ⟨_, b⟩ => b.toNat`; **or**
  * stating and proving a separate workhorse lemma along the lines of
    `gcd_while a b = RustM.ok (Nat.gcd … …) ` by induction on
    `b.toNat`, then deriving the four obligations as corollaries.

Both routes go beyond what the reference proof corpus demonstrates.
The boundary case `gcd_while 0 0 = RustM.ok 0` is computationally
tractable and is proved below; the three remaining obligations are
admitted with `sorry` and the technical situation documented in the
docstring of each.
-/

/-- **Failure condition (no panic / no divergence).**
    `gcd_while` always returns a successful result. The only fallible
    operation in the body is `a %? b`, but it is guarded by the loop
    condition `b != 0`, so the function never fails.

    *Status: admitted.* Proving totality requires a Hoare-triple about
    the underlying `while_loop`, which in turn needs a sound
    termination measure — but the source-provided measure is the
    constant `0`, which is unsound, so the standard
    `rust_primitives.hax.while_loop.spec` is unusable. A working
    proof would need to descend to `Spec.MonoLoopCombinator.while_loop`
    and supply `fun ⟨_, b⟩ => b.toNat` as the termination measure. -/
theorem gcd_while_total (a b : u64) :
    ∃ g, gcd_while.gcd_while a b = RustM.ok g := by
  sorry

/-- **Postcondition (boundary at `(0, 0)`).**
    By convention `gcd(0, 0) = 0`. This case must be stated separately
    because the `greatest` clause is vacuous when both inputs are zero
    (every natural number divides `0`).

    Proof: when `b = 0`, the loop's pure condition `b !=? 0` evaluates
    to `false` immediately, so the `Loop.MonoLoopCombinator.while_loop`
    takes the `done` branch on the very first iteration and returns
    `pure ⟨0, 0⟩`. The whole `gcd_while.gcd_while 0 0` term then
    reduces to `pure 0` by `native_decide` (the `partial_fixpoint`
    layer is reducible by the kernel after sufficient unfolding,
    because no loop iteration is taken). -/
theorem gcd_while_zero_zero :
    gcd_while.gcd_while (0 : u64) (0 : u64) = RustM.ok (0 : u64) := by
  native_decide

/-- **Postcondition (common divisor).**
    The returned value divides both inputs. Stated with `Nat` divisibility
    (`∣`), so the boundary case `gcd_while 0 0 = 0` is consistent
    (`0 ∣ 0` holds), while a returned `0` for any non-`(0, 0)` input would
    be ruled out (since `0 ∤ n` for `n > 0`).

    *Status: admitted.* The natural proof is to establish a workhorse
    lemma `∀ a b, gcd_while a b = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat))`
    by induction on `b.toNat` over the loop iterations, then derive
    `divides_both` from `Nat.gcd_dvd_left` / `Nat.gcd_dvd_right`. The
    workhorse lemma needs the loop invariant
    `Nat.gcd a.toNat b.toNat = Nat.gcd a₀.toNat b₀.toNat`, which in turn
    needs `Spec.MonoLoopCombinator.while_loop` with a hand-written
    termination measure (see `gcd_while_total`'s note). -/
theorem gcd_while_divides_both (a b g : u64)
    (h : gcd_while.gcd_while a b = RustM.ok g) :
    g.toNat ∣ a.toNat ∧ g.toNat ∣ b.toNat := by
  sorry

/-- **Postcondition (greatest).**
    No natural number strictly greater than the returned value divides
    both inputs. Excludes the degenerate `(0, 0)` case where every natural
    divides both inputs (handled by `gcd_while_zero_zero` instead).

    *Status: admitted.* Same situation as `gcd_while_divides_both`: the
    greatest-divisor postcondition follows from the workhorse lemma
    `gcd_while a b = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat))`
    via `Nat.dvd_gcd`, but that lemma needs the loop induction described
    in `gcd_while_total`'s note. -/
theorem gcd_while_greatest (a b g : u64)
    (h : gcd_while.gcd_while a b = RustM.ok g)
    (h_not_both_zero : a ≠ 0 ∨ b ≠ 0)
    (d : Nat) (hd : g.toNat < d) :
    ¬ (d ∣ a.toNat ∧ d ∣ b.toNat) := by
  sorry

end Gcd_whileObligations
