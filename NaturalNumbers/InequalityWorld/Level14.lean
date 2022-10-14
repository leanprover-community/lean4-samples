import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import AdditionWorld.Level2 -- add_assoc
namespace MyNat
open MyNat
/-!

# Inequality world.

## Level 14: `add_le_add_left`

I know these are easy and we've done several already, but this is one
of the axioms for an ordered commutative monoid! The nature of formalizing
is that we should formalize all "obvious" lemmas, and then when we're
actually using ` ≤` in real life, everything will be there. Note also,
of course, that all of these lemmas are already formalized in Lean's
maths library already, for Lean's inbuilt natural numbers.

## Lemma
If `a ≤ b` then for all `t`, `t+a ≤ t+b`.
-/
theorem add_le_add_left {a b : MyNat} (h : a ≤ b) (t : MyNat) :
  t + a ≤ t + b := by
  cases h with
  | _ c hc =>
    use c
    rw [hc]
    rw [add_assoc]

/-!
Next up [Level 15](./Level15.lean.md)
-/
