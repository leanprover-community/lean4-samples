import Mathlib.Tactic.Relation.Symm

/-!
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

`zero_ne_succ (a : MyNat) : 0 ≠ succ a`

We can simply use the `symm` tactic to flip this goal into
`succ a ≠ 0` which then matches our `zero_ne_succ` axiom.
-/