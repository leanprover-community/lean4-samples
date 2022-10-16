import MyNat.Addition
import MyNat.Multiplication
import AdditionWorld.Level1 -- zero_add
import AdditionWorld.Level2 -- add_assoc
namespace MyNat
open MyNat

/-!
# Multiplication World

## Level 4: `mul_add`

Where are we going? Well we want to prove `mul_comm`
and `mul_assoc`, i.e. that `a * b = b * a` and
`(a * b) * c = a * (b * c)`. But we *also* want to
establish the way multiplication interacts with addition,
i.e. we want to prove that we can "expand out the brackets"
and show `a * (b + c) = (a * b) + (a * c)`.
The technical term for this is "left distributivity of
multiplication over addition" (there is also right distributivity,
which we'll get to later).

Note the name of this proof -- `mul_add`. And note the left
hand side -- `a * (b + c)`, a multiplication and then an addition.
I think `mul_add` is much easier to remember than "left_distrib",
an alternative name for the proof of this lemma.

## Lemma

Multiplication is distributive over addition.
In other words, for all natural numbers `a`, `b` and `t`, we have
`t(a + b) = ta + tb`.
-/

lemma mul_add (t a b : MyNat) : t * (a + b) = t * a + t * b := by
  induction b with
  | zero =>
     rw [zero_is_0, add_zero, mul_zero, add_zero]
  | succ b ih =>
    rw [add_succ]
    rw [mul_succ]
    rw [ih]
    rw [mul_succ]
    rw [add_assoc]

def left_distrib := mul_add -- the "proper" name for this lemma


/-!
Next up is [Multiplication Level 5](./Level5.lean.md).
-/
