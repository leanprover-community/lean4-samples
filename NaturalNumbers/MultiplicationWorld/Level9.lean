import MyNat.Addition
import MyNat.Multiplication
import MultiplicationWorld.Level5
import MultiplicationWorld.Level8
namespace MyNat
open MyNat

/-!
# Multiplication World

## Level 9: `mul_left_comm`

You are equipped with

* `mul_assoc (a b c : MyNat) : (a * b) * c = a * (b * c)`
* `mul_comm (a b : MyNat) : a * b = b * a`

Re-read the docs for `rw` so you know all the tricks.
You can see them in the [Tactics section](../Tactics.lean.md) on the left.

## Lemma
For all natural numbers `a` `b` and `c`, we have `a(bc) = b(ac)`.
-/
lemma mul_left_comm (a b c : MyNat) : a * (b * c) = b * (a * c) := by
  rw [←mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]


/-!
And now you can teach the `simp` tactic these new tricks:
-/
attribute [simp] mul_assoc mul_comm mul_left_comm
/-!
and all of a sudden Lean can automatically do levels which are
very boring for a human, for example:
-/
example (a b c d e : MyNat) :
  (((a*b)*c)*d)*e=(c*((b*e)*a))*d := by
  simp

/-!
If you feel like attempting Advanced Multiplication world
you'll have to do [Function World](../FunctionWorld.lean.md) and the Proposition Worlds first.
These worlds assume a certain amount of mathematical maturity
(perhaps 1st year undergraduate level).

Your other possibility is [Power World](../PowerWorld.lean.md).
-/