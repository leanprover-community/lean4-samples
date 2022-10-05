import MyNat.Definition
import MyNat.Addition
import AdditionWorld.Level2Answer -- add_assoc
import AdditionWorld.Level4Answer -- add_comm
import AdditionWorld.Level5Answer -- succ_eq_add_one
open MyNat
-- import tactic.ring -- hide

/-

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
Similarly, if `h : a = b` then `rw [h]` will change `a`'s to `b`'s
and `rw [← h]` will change `b`'s to `a`'s.

Also, you can be (and will need to be, in this level) more precise
about where to rewrite theorems. `rw [add_comm]` will just find the
first `? + ?` it sees and swap it around. You can target more specific
additions like this: `rw [add_comm a]` will swap around
additions of the form `a + ?`, and `rw [add_comm a b]` will only
swap additions of the form `a + b`.

## Where next?

There are thirteen more levels about addition after this one, but before
you can attempt them you need to learn some more tactics. So after this
level you have a choice -- either move on to Multiplication World (which you can
solve with the tactics you know) or try Function World (and learn some new ones).
Other things, perhaps of interest
to some players, are mentioned below the lemma.

** Lemma**

For all natural numbers `a, b` and `c`, we have `a + b + c = a + c + b.`
-/
lemma add_right_comm (a b c : MyNat) : a + b + c = a + c + b := by
  sorry

/-
If you have got this far, then you have become very good at
manipulating equalities in Lean. You can also now collect
four collectibles (or `instance`s, as Lean calls them)

```
MyNat.add_semigroup -- (after level 2)
MyNat.add_monoid -- (after level 2)
MyNat.add_comm_semigroup MyNat (after level 4)
MyNat.add_comm_monoid -- (after level 4)
```

In Multiplication World you will be able to collect such
advanced collectibles as `MyNat.comm_semiring` and
`MyNat.distrib`, and then move on to power world and
the famous collectible at the end of it.

One last thing -- didn't you think that solving this level
`add_right_comm` was boring? Check out this AI that can do it for us.

The `simp` AI (it's just an advanced tactic really), and can nail some really
tedious-for-a-human-to-solve goals. For example, check out this one-line proof.
First you need to teach `simp` about the building blocks you have created so far:
-/
attribute [simp] zero_add add_assoc add_comm succ_add add_succ succ_eq_add_one one_eq_succ_zero

example (a b c d e : MyNat) :
  (((a+b)+c)+d)+e=(c+((b+e)+a))+d := by
  simp

-- BUGBUG: simp does not solve it!

/-
Imagine having to do that one by hand! The AI closes the goal
because it knows how to use associativity and commutativity
sensibly in a commutative monoid.

You are now done with addition world. You can now decide whether to press on with multiplication world and power world
(which can be solved with `rw`, `rfl` and `induction`), or to go on
to Function World where you can learn the tactics needed to prove
goals of the form `P → Q`, thus enabling you to solve more
advanced addition world levels such as `a + t = b + t → a = b`. Note that
Function World is more challenging mathematically; but if you can do Addition
World you can surely do Multiplication World and Power World.

-/