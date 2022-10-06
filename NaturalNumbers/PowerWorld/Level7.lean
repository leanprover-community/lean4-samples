import MyNat.Power
import MyNat.Multiplication
import PowerWorld.Level5 -- pow_add
namespace MyNat
open MyNat

/-!
# Power World

## Level 7: `pow_pow`

Boss level! What will the collectible be?

## Lemma
For all naturals `a`, `m`, `n`, we have `(a ^ m) ^ n = a ^ {mn}`.
-/
lemma pow_pow (a m n : MyNat) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero =>
    rw [zero_is_0]
    rw [mul_zero]
    repeat rw [pow_zero]
  | succ n ih =>
    rw [pow_succ]
    rw [ih]
    rw [mul_succ]
    rw [pow_add]


/-!
Apparently Lean can't find a collectible, even though you feel like you
just finished power world so you must have proved *something*. What should the
collectible for this level be called?

But what is this? It's one of those twists where there's another
boss after the boss you thought was the final boss! Go to the next
level!

Next up [Level 8](./Level8.lean.md)
-/