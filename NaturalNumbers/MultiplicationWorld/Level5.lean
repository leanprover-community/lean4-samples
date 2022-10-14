import MyNat.Addition
import MyNat.Multiplication
import MultiplicationWorld.Level1 -- zero_mul
import MultiplicationWorld.Level4 -- mul_add
namespace MyNat
open MyNat

/-!
# Multiplication World

## Level 5: `mul_assoc`

We now have enough to prove that multiplication is associative.

## Random tactic hints

Did you know you can [repeat](../Tactics/repeat.lean.md) a tactic as many times as necessary
to complete the goal?

## Lemma

Multiplication is associative.
In other words, for all natural numbers `a`, `b` and `c`, we have
` (ab)c = a(bc). `
-/
lemma mul_assoc (a b c : MyNat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
    rw [zero_is_0]
    repeat
      rw [mul_zero]
  | succ c ih =>
    rw [mul_succ]
    rw [mul_succ]
    rw [ih]
    rw [mul_add]

/-!
A mathematician could now remark that you have proved that the natural
numbers form a monoid under multiplication.
-/

-- instance : AddMonoid MyNat where
--   add_zero := add_zero
--   zero_add := zero_add
--   add_assoc := add_assoc
--   nsmul :=  λ x y => (myNatFromNat x) * y
--   nsmul_zero' := zero_mul
--   nsmul_succ' n x := by
--     simp

-- BUGBUG: complete these instances...


/-!
Next up is [Multiplication Level 6](./Level6.lean.md).
-/