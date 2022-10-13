import MyNat.Definition
import MyNat.Addition -- add_zero
import AdvancedAdditionWorld.Level6 -- add_left_cancel
namespace MyNat
open MyNat

/-!

# Advanced Addition World

## Level 8: `eq_zero_of_add_right_eq_self`

The lemma you're about to prove will be useful when we want to prove that `≤` is antisymmetric.
There are some wrong paths that you can take with this one.

## Lemma

If `a` and `b` are natural numbers such that
` a + b = a, ` then `b = 0`.
-/

lemma eq_zero_of_add_right_eq_self {a b : MyNat} : a + b = a → b = 0 := by
  intro h
  apply add_left_cancel a
  rw [h]
  rw [add_zero]

/-!
Remember from [FunctionWorld Level 4]()../FunctonWorld/Level4.lean.md) that the
`apply` tactic is can construct the path backwards?  Well when we use it with
`add_left_cancel a` it results in the opposite of cancellation, it
results in _adding a to both sides_ changing the goal from `⊢ b = 0`
to `⊢ a + b = a + 0`.  This then allows us to use our hypothesis `h : a + b = a`
in `rw` to complete the proof.

Next up [Level 9](./Level9.lean.md)
-/
