import MyNat.Addition
namespace MyNat
open MyNat
/-!
# Addition World

## Level 5: `succ_eq_add_one`

-/
axiom one_eq_succ_zero : (1 : MyNat) = MyNat.succ 0
/-!
We've just added `one_eq_succ_zero` (a statement that `1 = succ 0`).
This is not a proof it is an axiom.  In Lean an `axiom` tells Lean
don't go looking for a proof for this fact, just trust me, it's true.
So you must be very careful in how you use `axiom` because it can
lead to inconsistencies in subsequent proofs if your axiom contains
an error.

Levels 5 and 6 are the two last levels in Addition World.
Level 5 involves the number `1`. When you see a `1` in your goal,
you can write `rw [one_eq_succ_zero]` to get back
to something which only mentions `0`. This is a good move because `0` is easier for us to
manipulate than `1` right now, because we have
some theorems about `0` (`zero_add`, `add_zero`), but, other than `1 = succ 0`,
no theorems at all which mention `1`. Let's prove one now.

## Theorem

For any natural number `n`, we have `succ n = n + 1`.
-/
theorem succ_eq_add_one (n : MyNat) : succ n = n + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rfl

/-!
Note that `lemma` and `theorem` are the same thing and can be used
interchangeably.

Hint: if you use proof by induction, but then find you don't need the hypothesis
in the inductive step, then you probably didn't need proof by induction.

Press on to [level 6](./Level6.lean.md).
-/