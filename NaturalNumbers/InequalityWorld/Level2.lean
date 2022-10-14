import MyNat.Definition
import MyNat.Addition -- add_zero
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import Mathlib.Tactic.Relation.Rfl -- rfl tactic
import AdditionWorld.Level4 -- add_comm
namespace MyNat
open MyNat
/-!

# Inequality world.

Here's a nice easy one.

## Level 2: le_refl

## Lemma :
The `≤` relation is reflexive. In other words, if `x` is a natural number,
then `x ≤ x`.
-/
lemma le_refl (x : MyNat) : x ≤ x := by
  use 0

/-!
## Upgrading the `refl` tactic

Now with the following incantation you can teach the MathLib refl tactic
about our new lemma.
-/
attribute [refl] MyNat.le_refl
/-!
Now we find that the `rfl` tactic will close all goals
of the form `a ≤ a` as well as all goals of the form `a = a`.
-/
example : (0 : MyNat) ≤ 0 := by
  rfl

/-
## Pro tip

-- BUGBUG in lean4 `use 0` closes the proof, so no need for all this stuff
below -- so I need to move this info to another place where it makes sense.

Did you skip `rw [le_iff_exists_add]` in your proof of `le_refl` above?
Instead of `rw [add_zero]` or `ring` or `exact add_zero x` at the end there,
what happens if you just try `refl`? The *definition* of `x + 0` is `x`,
so you don't need to `rw add_zero` either! The proof

```
use 0,
refl,
```

works.

The same remarks are true of
`add_succ`, `mul_zero`, `mul_succ`, `pow_zero` and `pow_succ`. All of those
theorems are true *by definition*. The same is *not* true however of `zero_add`;
the theorem `0 + x = x` was proved by induction on `x`,
and in particular it is not true by *definition*.

Definitional equality is of great importance
to computer scientists, but mathematicians are much more fluid with their idea
of a definition -- a concept can simultaneously have three equivalent definitions
in a maths talk, as long as they're all logically equivalent. In Lean, a definition
is *one thing*, and definitional equality is a subtle concept which depends on
exactly which definition you chose. `add_comm` is certainly not true by definition,
which means that if we had decided to define `a ≤ b` by `∃ c, b = c + a` (rather
than `a + c`) all the same theorems would be true, but `refl` would work in
different places. `refl` closes a goal of the form `X = Y` if `X` and `Y` are
definitionally equal.


Next up [Level 3](./Level3.lean.md)
-/
