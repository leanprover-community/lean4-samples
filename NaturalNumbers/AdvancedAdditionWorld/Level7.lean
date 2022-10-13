import MyNat.Definition
import AdditionWorld.Level4 -- add_comm
import AdvancedAdditionWorld.Level5 -- add_right_cancel
namespace MyNat
open MyNat

/-!

# Advanced Addition World

## Level 7: `add_right_cancel_iff`

It's sometimes convenient to have the "if and only if" version
of theorems like `add_right_cancel`. Remember that you can use `split`
to split an `↔` goal into the `→` goal and the `←` goal.

## Pro tip:

Notice `exact add_right_cancel _ _ _` means "let Lean figure out the missing inputs"
so we don't have to spell it out like we did in Level 6.

## Theorem
For all naturals `a`, `b` and `t`, `a + t = b + t ↔ a = b.`
-/
theorem add_right_cancel_iff (t a b : MyNat) :  a + t = b + t ↔ a = b := by
  constructor
  exact add_right_cancel _ _ _
  intro h
  rw [h]

/-!
Next up [Level 8](./Level8.lean.md)
-/
