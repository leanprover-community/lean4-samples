import MyNat.Definition
namespace MyNat
/-!

# Tutorial world

## Level 2: The `rewrite` tactic

The `rewrite` tactic is the way to "substitute in" the value of a variable. In general, if you have a
hypothesis of the form `A = B`, and your goal mentions the left hand side `A` somewhere, then the
rewrite tactic will replace the `A` in your goal with a `B`. Below is a theorem which cannot be proved
using `rfl` -- you need a `rewrite` first.

Take a look in the InfoView at what you have. The variables
`x` and `y` are natural numbers, and there is a proof `h` that `y = x + 7`.
Your goal then is to prove that `2y = 2(x + 7)`. This goal is obvious -- you just substitute in
`y = x + 7` and you're done. In Lean, you do this substitution using the `rewrite` tactic.

## Lemma

If `x` and `y` are natural numbers, and `y = x + 7`, then `2y = 2(x + 7)`.
-/
lemma example2 (x y : MyNat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rewrite [h]
  rfl

/-!
Did you see what happened to the goal? (Put your cursor at the end of the `rewrite` line).
The goal doesn't close, but it *changes* from `⊢ 2 * y = 2 * (x + 7)` to `⊢ 2 * (x + 7) = 2 * (x + 7)`.
And since these are now identical you can just close this goal with `rfl`.

You should now see "Goals accomplished 🎉" (with cursor at the end of the `rfl` line).
The square brackets here is a `List` object
because `rewrite` can rewrite using multiple hypotheses in sequence.

If you are reading this book online you can move the mouse over each bubble that is
added to the end of each line (that look like this: <span class="alectryon-bubble"></span>)
to see what the tactic state is at that point in the proof.

The other way you know the goal is complete is to look a the Visual Studio Code
Problems list window, if there are no error saying "unsolved goals" then you are done.

The documentation for `rewrite` will appear when you hover the mouse over it.

Now, Lean has another similar tactic named `rw` which does both the `rewrite`
and the `rfl`.  Try changing to `rw` above and you will see the `rfl` is
no longer needed.

## Details

Now you are ready for [Level3.lean](./Level3.lean.md).
-/