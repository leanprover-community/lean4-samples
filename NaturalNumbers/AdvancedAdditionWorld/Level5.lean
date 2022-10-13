import MyNat.Definition
import MyNat.Addition -- add_zero
import AdvancedAdditionWorld.Level1 -- succ_inj
namespace MyNat
open MyNat

/-!

# Advanced Addition World

## Level 5: `add_right_cancel`

The theorem `add_right_cancel` is the theorem that you can cancel on the right
when you're doing addition -- if `a + t = b + t` then `a = b`. After `intro h`
I'd recommend induction on `t`. Don't forget that `rw [add_zero] at h` can be used
to do rewriting of hypotheses rather than the goal.

## Theorem
On the set of natural numbers, addition has the right cancellation property.
In other words, if there are natural numbers `a, b` and `c` such that
` a + t = b + t ` then we have `a = b`.
-/
theorem add_right_cancel (a t b : MyNat) : a + t = b + t → a = b := by
  intro h
  induction t with
  | zero =>
    rw [zero_is_0] at h
    rw [add_zero] at h
    rw [add_zero] at h
    exact h
  | succ d ih =>
    apply ih
    rw [add_succ] at h
    rw [add_succ] at h
    exact succ_inj h

/-!
Next up [Level 6](./Level6.lean.md)
-/
