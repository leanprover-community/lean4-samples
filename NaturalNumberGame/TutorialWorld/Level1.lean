import MyNat.Definition
/-!
# Tutorial world

## Level 1: the rfl tactic

Let's learn some tactics! Let's start with the `rfl` tactic. `rfl` stands for "reflexivity", which is
a fancy way of saying that it will prove any goal of the form `A = A`. It doesn't matter how
complicated `A` is, all that matters is that the left hand side is exactly equal to the right hand
side (a computer scientist would say "definitionally equal"). I really mean "press the same buttons
on your computer in the same order" equal. For example, `x * y + z = x * y + z` can be proved by `rfl`,
but `x + y = y + x` cannot.

Each level in this game involves proving a theorem or a lemma (a lemma is just a baby theorem). The
goal of the theorem will be a mathematical statement with a `⊢` just before it. We will use tactics
to manipulate and ultimately close (i.e. prove) these goals.

> Note that while lean4 does not define the keyword `lemma` it has been added to the `mathlib4`
library so it is coming from the `import Mathlib.Tactic.Basic` that you see above.

Let's see `rfl` in action! At the bottom of the text in this box, there's a lemma, which says that
if `x`, `y` and `z` are natural numbers then `xy + z = xy + z`. Locate this lemma (if you can't see
the lemma and these instructions at the same time, make this box wider by dragging the sides). Let's
supply the proof. Click on the word sorry and then delete it. When the system finishes being busy,
you'll be able to see your goal in the Visual Studio Code InfoView.

Remember that the goal is the thing with the unicode symbol `⊢` just before it. The goal in this
case is `x * y + z = x * y + z`, where `x`, `y` and `z` are some of your very own natural numbers.
That's a pretty easy goal to prove -- you can just prove it with the `rfl` tactic. Where it used to
say sorry, write `rfl`.

**Lemma**

For all natural numbers `x`, `y` and `z`, we have `xy + z = xy + z`.
-/

lemma example1 (x y z : MyNat) : x * y + z = x * y + z := by
  sorry
/-!
If all goes well Lean will print `Goals accomplished 🎉` in the InfoView.
You just did the first level of the tutorial!

For each level, the idea is to get Lean into this state: with the InfoView saying "`Goals accomplished 🎉`"
when the cursor is placed at the end of the line that completes the proof.

If you want to be reminded about the `rfl` tactic, you can hover the mouse over the `rfl` keyword and
a tooltip will appear with information about this tactic.  You can also press F12 to jump to the
definition of that tactic were there will be lots more handy information.

Now click on "next level" in the top right of your browser to go onto the second level of tutorial
world, where we'll learn about the rw tactic.

Now you are ready for [Level2.lean](./Level2.lean).
-/