import MyNat.Definition
/-!

# Tutorial world

## Level 2: The rewrite ('rw') tactic

The rewrite tactic is the way to "substitute in" the value of a variable. In general, if you have a
hypothesis of the form `A = B`, and your goal mentions the left hand side `A` somewhere, then the
rewrite tactic will replace the `A` in your goal with a `B`. Below is a theorem which cannot be proved
using `rfl` -- you need a rewrite first.

Delete the sorry and take a look in the InfoView at what we have. The variables
`x` and `y` are natural numbers, and we have a proof `h` that `y = x + 7`.
Our goal is to prove that `2y = 2(x + 7)`. This goal is obvious -- we just substitute in
`y = x + 7` and we're done. In Lean, we do this substitution using the `rw` tactic.
So complete your proof with `rw [h]`

**Lemma**

If `x` and `y` are natural numbers, and `y = x + 7, then `2y = 2(x + 7)`.
-/
lemma example2 (x y : MyNat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  sorry

/-!
You should now see "Goals accomplished 🎉".  Notice you did not have to add `rfl` to this
proof because `rw` does that automatically.  The square brackets here is a `list` object
because `rw` can rewrite according to multiple hypotheses at once.

The other way you know the goal is complete is to look a the Visual Studio Code
Problems list window, if there are no error listed there then you are done.

The documentation for `rw` will appear when you hover the mouse over it.


Now you are ready for [Level3.lean](./Level3.lean).
-/