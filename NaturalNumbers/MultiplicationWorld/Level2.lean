import MyNat.Addition
import MyNat.Multiplication
import AdditionWorld.Level1 -- zero_add
import AdditionWorld.Level5 -- one_eq_succ_zero
namespace MyNat
open MyNat

/-!
# Multiplication World

## Level 2: `mul_one`

In this level we'll need to use

* `one_eq_succ_zero : 1 = succ 0`

which was mentioned back in [Addition World Level 5](../AdditionWorld/Level5.lean.md) and which will
be a useful thing to rewrite right now, as we begin to prove a couple of lemmas about how `1`
behaves with respect to multiplication.

## Lemma

For any natural number `m`, we have `m * 1 = m`.
-/
lemma mul_one (m : MyNat) : m * 1 = m := by
  rw [one_eq_succ_zero]
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]

/-!
Notice how all our theorems are nicely building on each other.

Next up is [Multiplication Level 3](./Level3.lean.md).
-/