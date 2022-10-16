import MyNat.Definition
import MyNat.Addition
import AdditionWorld.Level6
import AdvancedAdditionWorld.Level1 -- succ_inj
import AdvancedAdditionWorld.Level3 -- succ_eq_succ_of_eq
namespace MyNat
open MyNat

/-!

# Advanced Addition World

## Level 4: `eq_iff_succ_eq_succ`

Here is an `iff` goal. You can split it into two goals (the implications in both
directions) using the `constructor` tactic, which is how you're going to have to start.

`constructor`

Now you have two goals. The first is exactly `succ_inj` so you can close
it with

`exact succ_inj`

and the second one you could solve by looking up the name of the theorem
you proved in the last level and doing `exact <that name>`, or alternatively
you could get some more `intro` practice and see if you can prove it
using `intro` and `rw`.

Remember that `succ_inj` is `succ a = succ b → a = b`.

## Theorem
Two natural numbers are equal if and only if their successors are equal.
-/
theorem succ_eq_succ_iff (a b : MyNat) : succ a = succ b ↔ a = b := by
  constructor
  exact succ_inj
  exact succ_eq_succ_of_eq


/-!
Next up [Level 5](./Level5.lean.md).
-/
