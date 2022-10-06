import MyNat.Addition
import MyNat.Multiplication
import MultiplicationWorld.Level1
import MultiplicationWorld.Level6
namespace MyNat
open MyNat

/-!
# Multiplication World

## Level 8: `mul_comm`

Finally, the boss level of multiplication world. But you are well-prepared for it -- you have
`zero_mul` and `mul_zero`, as well as `succ_mul` and `mul_succ`. After this level you can of course
throw away one of each pair if you like, but I would recommend you hold on to them, sometimes it's
convenient to have exactly the right tools to do a job.

## Lemma
Multiplication is commutative.
-/
lemma mul_comm (a b : MyNat) : a * b = b * a := by
  induction b with
  | zero =>
    rw [zero_is_0]
    rw [zero_mul]
    rw [mul_zero]
  | succ b ih =>
    rw [succ_mul]
    rw [←ih]
    rw [mul_succ]

/-!
You've now proved that the natural numbers are a commutative semiring!
That's the last collectible in Multiplication World.
-/
-- instance mynat.comm_semiring : comm_semiring mynat := by structure_helper
-- BUGBUG
/-!
But don't leave multiplication just yet -- prove `mul_left_comm`, the last
level of the world, and then we can beef up the power of `simp`.

On to [Level 9](./Level9.lean.md)
-/
