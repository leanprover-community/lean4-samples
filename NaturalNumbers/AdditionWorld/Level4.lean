import MyNat.Addition -- imports addition.
import AdditionWorld.Level1 -- zero_add
import AdditionWorld.Level3 -- succ_add
namespace MyNat
open MyNat

/-!
# Addition World

## Level 4: `add_comm`

[boss battle music]

Look in Theorem statements -> Addition world to see the proofs you have.
These should be enough.

## Lemma

On the set of natural numbers, addition is commutative.
In other words, for all natural numbers `a` and `b`, we have `a + b = b + a.`
-/
lemma add_comm (a b : MyNat) : a + b = b + a := by
  induction b with
  | zero =>
    rw [zero_is_0]
    rw [add_zero]
    rw [zero_add]
  | succ b ih =>
    rw [add_succ]
    rw [ih]
    rw [succ_add]

/-!

If you are keeping up so far then nice! You're nearly ready to make a choice:
Multiplication World or Function World. But there are just a couple
more useful lemmas in Addition World which you should prove first.

Press on to [level 5](./Level5.lean.md).

-/