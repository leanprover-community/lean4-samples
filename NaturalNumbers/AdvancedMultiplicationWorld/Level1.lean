import MyNat.Definition
import MyNat.Addition -- add_succ
import MyNat.Multiplication -- mul_succ
import AdvancedAdditionWorld.Level9 -- succ_ne_zero
namespace MyNat
open MyNat
/-!
# Advanced Multiplication World

## Level 1: `mul_pos`

Recall that if `b : MyNat` is a hypothesis and you do `cases b with`,
your one goal will split into two goals,
namely the cases `b = 0` and `b = succ n`. So `cases` here is like
a weaker version of induction (you don't get the inductive hypothesis).

## Tricks

1) if your goal is `⊢ X ≠ Y` then `intro h` will give you `h : X = Y` and
a goal of `⊢ false`. This is because `X ≠ Y` *means* `(X = Y) → false`.
Conversely if your goal is `false` and you have `h : X ≠ Y` as a hypothesis
then `apply h` will work backwards and turn the goal into `X = Y`.

2) if `hab : succ (3 * x + 2 * y + 1) = 0` is a hypothesis and your goal is `⊢ false`,
then `exact succ_ne_zero _ hab` will solve the goal, because Lean will figure
out that `_` is supposed to be `3 * x + 2 * y + 1`.

# Theorem
The product of two non-zero natural numbers is non-zero.
-/
theorem mul_pos (a b : MyNat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  intros ha hb
  intro hab
  cases b with
  | zero =>
    apply hb
    rfl
  | succ b' =>
    rw [mul_succ] at hab
    apply ha
    cases a with
    | zero =>
      rfl
    | succ a' =>
      rw [add_succ] at hab
      exfalso
      exact succ_ne_zero _ hab
/-!

Next up [Level 2](./Level2.lean.md)
-/
