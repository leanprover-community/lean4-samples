import MyNat.Definition
import MyNat.Addition
namespace MyNat
open MyNat

/-!

# Advanced Addition World

## Level 3: `succ_eq_succ_of_eq`.

We are going to prove something completely obvious: if `a=b` then
`succ a = succ b`. This is *not* `succ_inj`!
This is trivial -- we can just rewrite our proof of `a=b`.
But how do we get to that proof? Use the `intro` tactic.

## Theorem
For all naturals `a` and `b`, `a = b ⟹ succ a = succ b`.
-/
theorem succ_eq_succ_of_eq {a b : MyNat} : a = b → succ a = succ b := by
  intro h
  rw [h]

/-!
Next up [Level 4](./Level4.lean.md)
-/
