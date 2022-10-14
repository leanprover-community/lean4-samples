import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import AdditionWorld.Level4 -- add_comm
namespace MyNat
open MyNat

/-!

# Inequality world.

## Level 1: the [`use` tactic](../Tactics/use.lean.md)

The goal below is to prove `x ≤ 1+x` for any natural number `x`.
First let's turn the goal explicitly into an existence problem with

`rw [le_iff_exists_add]`

and now the goal has become `∃ c : MyNat, 1 + x = x + c`. Clearly
this statement is true, and the proof is that `c=1` will work (we also
need the fact that addition is commutative, but we proved that a long
time ago). How do we make progress with this goal?

The `use` tactic can be used on goals of the form `∃ c, ...`. The idea
is that we choose which natural number we want to use, and then we use it.
So try

`use 1`

and now the goal becomes `⊢ 1 + x = x + 1`. You can solve this by
`exact add_comm 1 x`, or if you are lazy you can just use the `ring` tactic,
which is a powerful AI which will solve any equality in algebra which can
be proved using the standard rules of addition and multiplication. Now
look at your proof. We're going to remove a line.

## Important

An important time-saver here is to note that because `a ≤ b` is *defined*
as `∃ c : MyNat, b = a + c`, you *do not need to write* `rw [le_iff_exists_add]`.
The `use` tactic will work directly on a goal of the form `a ≤ b`. Just
use the difference `b - a` (note that we have not defined subtraction so
this does not formally make sense, but you can do the calculation in your head).
If you have written `rw [le_iff_exists_add]` below, then just put two minus signs `--`
before it and comment it out. See that the proof still compiles.

## Lemma : one_add_le_self
If `x` is a natural number, then `x ≤ 1+x`.
-/
lemma one_add_le_self (x : MyNat) : x ≤ 1 + x := by
  rw [le_iff_exists_add]
  use 1
  rw [add_comm]

/-!


Next up [Level 2](./Level2.lean.md)

-/
