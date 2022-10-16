import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import AdvancedAdditionWorld.Level1 --  succ_inj
import AdvancedAdditionWorld.Level9 --  zero_ne_succ
namespace MyNat
open MyNat

/-!

# Inequality World

## Level 13: `not_succ_le_self`

Turns out that `¬ P` is *by definition* `P → False`, so you can just
start this one with `intro h` if you like.

##  Lemma: `not_succ_le_self`
For all naturals `a`, `succ a` is not at most `a`.
-/
theorem not_succ_le_self (a : MyNat) : ¬ (succ a ≤ a) := by
  intro h
  cases h with
  | _ c h =>
    induction a with
    | zero =>
      rw [succ_add] at h
      exact zero_ne_succ _ h
    | succ d hd =>
      rw [succ_add] at h
      apply hd
      apply succ_inj
      exact h

/-!

## Pro tip:

The `conv` tactic allows you to perform targeted rewriting on a goal or hypothesis, by focusing
on particular subexpressions.

```
  conv =>
    lhs
    rw hc
```

This is an incantation which rewrites `hc` only on the left hand side of the goal.
You didn't need to use `conv` in the above proof
but it's a helpful trick when `rw` is rewriting too much.

For a deeper discussion on `conv` see [Conversion Tactic Mode](https://leanprover.github.io/theorem_proving_in_lean4/conv.html).


Next up [Level 14](./Level14.lean.md).
-/
