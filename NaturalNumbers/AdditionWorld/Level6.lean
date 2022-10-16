import MyNat.Addition
import AdditionWorld.Level2 -- add_assoc
import AdditionWorld.Level4 -- add_comm
import AdditionWorld.Level5 -- succ_eq_add_one
namespace MyNat
open MyNat

/-!

# Addition World

## Level 6: `add_right_comm`

Lean sometimes writes `a + b + c`. What does it mean? The convention is
that if there are no brackets displayed in an addition formula, the brackets
are around the left most `+` (Lean's addition is "left associative").
So the goal in this level is `(a + b) + c = (a + c) + b`. This isn't
quite `add_assoc` or `add_comm`, it's something you'll have to prove
by putting these two theorems together.

If you hadn't picked up on this already, `rw [add_assoc]` will
change `(x + y) + z` to `x + (y + z)`, but to change it back
you will need `rw [← add_assoc]`. Get the left arrow by typing `\l`
then the space bar (note that this is L for left, not a number 1).
Similarly, if `h : a = b` then `rw [h]` will change `a`s to `b`s
and `rw [← h]` will change `b`s to `a`s.

Also, you can be (and will need to be, in this level) more precise
about where to rewrite theorems. `rw [add_comm]` will just find the
first `? + ?` it sees and swap it around. You can target more specific
additions like this: `rw [add_comm a]` will swap around
additions of the form `a + ?`, and `rw [add_comm a b]` will only
swap additions of the form `a + b`.

## Where next?

There are thirteen more levels about addition after this one, but before
you can attempt them you need to learn some more tactics. So after this
level you have a choice -- either move on to
[Multiplication World](../MultiplicationWorld.lean.md) (which you can
solve with the tactics you know) or try
[Function World](../FunctionWorld.lean.md) (and learn some new ones).
Other things, perhaps of interest
to some players, are mentioned below the lemma.

## Lemma

For all natural numbers `a, b` and `c`, we have `a + b + c = a + c + b`.
-/
lemma add_right_comm (a b c : MyNat) : a + b + c = a + c + b := by
  rw [add_assoc]
  rw [add_comm b c]
  rw [←add_assoc]

/-!
If you have got this far, then you have become very good at manipulating equalities in Lean. You can
also now connect four handy type class `instances` to your `MyNat` type as follows:

-/
-- instance : AddSemigroup MyNat where
--   add_assoc := add_assoc

-- instance : AddCommSemigroup MyNat where
--   add_comm := add_comm

-- instance : AddMonoid MyNat where
--   nsmul :=  λ x y => (myNatFromNat x) * y
--   nsmul_zero' := MyNat.zero_mul
--   nsmul_succ' n x := by
--     show ofNat (MyNat.succ n) * x = x + MyNat n * x
--     rw [MyNat.ofNat_succ, MyNat.add_mul, MyNat.add_comm, MyNat.one_mul]

-- instance : AddCommMonoid MyNat where
--   zero_add := zero_add
--   add_zero := add_zero
--   add_comm := add_comm
--   nsmul_zero' := ...
--   nsmul_succ' := ...

-- BUGBUG: really? These last two require theorems about multiplication?
-- like add_mul and zero_mul, which is dependent on mul_comm...?
/-!

In Multiplication World you will be able to collect such
advanced collectibles as `MyNat.comm_semiring` and
`MyNat.distrib`, and then move on to [Power World](../PowerWorld.lean.md) and
the famous collectible at the end of it.

One last thing -- didn't you think that solving this level
`add_right_comm` was boring? Check out this AI that can do it for us.

The `simp` AI (it's just an advanced tactic really), and can nail some really
tedious-for-a-human-to-solve goals. For example, check out this one-line proof.
First you need to teach `simp` about the building blocks you have created so far:
-/

lemma add_left_comm (a b c : MyNat) : a + (b + c) = b + (a + c) := by
  rw [←add_assoc]
  rw [add_comm a]
  rw [add_assoc]

attribute [simp] add_assoc add_comm add_left_comm

example (a b c d e : MyNat) :
  (((a+b)+c)+d)+e=(c+((b+e)+a))+d := by
  simp

/-!
Imagine having to do that one by hand! The AI closes the goal because it knows how to use
associativity and commutativity sensibly in a commutative monoid.

For more info see the [simp tactic](../Tactics/simp.lean.md).

You are now done with addition world. You can now decide whether to press on with
[Multiplication World](../MultiplicationWorld.lean.md) and [Power World](../PowerWorld.lean.md)
(which can be solved with `rw`, `rfl` and `induction`), or to go on to
[Function World](../FunctionWorld.lean.md) where you can learn the tactics needed to prove goals of the form `P → Q`, thus
enabling you to solve more advanced addition world levels such as `a + t = b + t → a = b`. Note that
[Function World](../FunctionWorld.lean.md) is more challenging mathematically;
but if you can do Addition World you can surely
do [Multiplication World](../MultiplicationWorld.lean.md) and [Power World](../PowerWorld.lean.md).

-/