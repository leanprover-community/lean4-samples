import AdditionWorld.Level1
import AdditionWorld.Level2
import AdditionWorld.Level3
import AdditionWorld.Level4
import AdditionWorld.Level5
import AdditionWorld.Level6

/-!
# Addition World

Welcome to Addition World. If you've done all four levels in [Tutorial
World](../TutorialWorld/Level1.lean.md) and know about `rewrite`, `rw` and `rfl`, then you're in the
right place. We'll use `rw` from her on out just for convenience.  Here's a reminder of the things
you're now equipped with which we'll need in this world.

## Data:

  * a type called `MyNat`
  * a term `0 : MyNat`, interpreted as the number zero.
  * a function `succ : MyNat → MyNat`, with `succ n` interpreted as "the number after `n`".
  * Usual numerical notation 0,1,2 etc (although 2 onwards will be of no use to us until much later ;-) ).
  * Addition (with notation `a + b`).

## Theorems:

  * `add_zero (a : MyNat) : a + 0 = a`. Use with `rw [add_zero]`.
  * `add_succ (a b : MyNat) : a + succ b = succ (a + b)`. Use with `rw [add_succ]`.
  * The principle of mathematical induction. Use with `induction` (see below).


## Tactics:

  * `rfl` :  proves goals of the form `X = X`.
  * `rw [h]` : if h is a proof of `A = B`, changes all A's in the goal to B's.
  * `induction n with ...` : we're going to learn this right now.

## Important thing

This is a *really* good time to check you can get "mouse hover help on anything in the Lean program.
If you hover over 'rfl' you get information on that tactic.  You can also press F12 to jump
right into the definition of all the helpers functions we use here.

On to [Addition World Level 1](./AdditionWorld/Level1.lean.md).
-/