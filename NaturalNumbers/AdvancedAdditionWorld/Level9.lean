import MyNat.Definition
import MyNat.Addition
import MyNat.Symm -- symm
namespace MyNat
open MyNat

axiom zero_ne_succ (a : MyNat) : 0 ≠ succ a

/-!

# Advanced Addition World

## Level 9: `succ_ne_zero`

## Tactic : symm

## Summary

`symm` turns goals of the form `⊢ A = B` to `⊢ B = A`.
This tactic is extensible, meaning you can add new `@[symm]`
attributes to things to teach `symm` new tricks, like we
did with the `simp` tactic.  To teach it how to deal with
`≠` we write this:
-/

@[symm] def neqSymm {α : Type} (a b: α) : a ≠ b → b ≠ a := Ne.symm

/-!

Levels 9 to 13 introduce the last axiom of Peano, namely
that `0 ≠ succ a`. The proof of this is called `zero_ne_succ a`.

`zero_ne_succ (a : MyNat) : 0 ≠ succ(a)`

We can simply use the `symm` tactic to flip this goal into
`succ a ≠ 0` which then matches our `zero_ne_succ` axiom.

## Theorem : succ_ne_zero
Zero is not the successor of any natural number.
-/

-- TODO switch to official Mathlib `symm` tactic when this PR goes in:
-- https://github.com/leanprover-community/mathlib4/pull/253/files

theorem succ_ne_zero (a : MyNat) : succ a ≠ 0 := by
  symm
  apply (zero_ne_succ a)

/-!
Next up [Level 10](./Level10.lean.md)
-/
