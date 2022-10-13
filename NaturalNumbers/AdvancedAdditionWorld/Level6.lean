import MyNat.Definition
import AdditionWorld.Level4 -- add_comm
import AdvancedAdditionWorld.Level5 -- add_right_cancel
namespace MyNat
open MyNat

/-!

# Advanced Addition World

## Level 6: `add_left_cancel`

The theorem `add_left_cancel` is the theorem that you can cancel on the left
when you're doing addition -- if `t + a = t + b` then `a = b`.
There is a three-line proof which ends in `exact add_right_cancel a t b` (or even
`exact add_right_cancel _ _ _`); this
strategy involves changing the goal to the statement of `add_right_cancel`.

## Theorem : add_left_cancel
On the set of natural numbers, addition has the left cancellation property.
In other words, if there are natural numbers `a, b` and `t` such that
if `t + a = t + b` then we have `a = b`.
-/
theorem add_left_cancel (t a b : MyNat) : t + a = t + b → a = b := by
  rw [add_comm]
  rw [add_comm t]
  exact add_right_cancel a t b


/-!
Next up [Level 7](./Level7.lean.md)
-/
