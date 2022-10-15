import MyNat.Addition
namespace MyNat
open MyNat
/-!

# Tutorial World

## Level 4: addition

We have a new import -- the definition of addition.

Peano defined addition `a + b` by induction on `b`, or, more precisely, by recursion on `b`. He first
explained how to add 0 to a number: this is the base case.

- `add_zero (a : MyNat) : a + 0 = a`

We will call this theorem `add_zero`. More precisely, `add_zero` is the name of the _proof_ of the
theorem. Note the name of this proof. Mathematicians sometimes call it "Lemma 2.1" or "Hypothesis
P6" or something. But computer scientists call it `add_zero` because it tells you what the answer to
"x add zero" is. It's a much better name than "Lemma 2.1". Even better, you can use the `rewrite` tactic
with `add_zero`. If you ever see `x + 0` in your goal, `rewrite [add_zero]` should simplify it to `x`. This is
because `add_zero` is a proof that `x + 0 = x` (more precisely, `add_zero x` is a proof that `x + 0 = x` but
Lean can figure out the `x` from the context).

Now here's the inductive step. If you know how to add `d` to `a`, then Peano tells you how to add
`succ d` to `a`. It looks like this:

- `add_succ (a d : MyNat) : a + (succ d) = succ (a + d)`

What's going on here is that we assume `a + d` is already defined, and we define `a + (succ d)` to
be the number after it. Note the name of this proof too -- `add_succ` tells you how to add a successor
to something. If you ever see `... + succ ...` in your goal, you should be able to use `rewrite [add_succ]`, to
make progress.

## Lemma

For all natural numbers `a`, we have `a + (succ 0) = succ a`.
-/
lemma add_succ_zero (a : MyNat) : a + (succ 0) = succ a := by
  rewrite [add_succ]
  rewrite [add_zero]
  rfl

/-!
Do you see that the goal at the end of the first `rewrite` now mentions `... + 0 ...`? So this
matches the `add_zero` theorem so you can now add the `rewrite [add_zero]`.

After the `rfl` the proof is now complete: "Goals accomplished 🎉".
Note that because `rewrite` takes a list, you can also write the above two lines in one
using `rewrite [add_succ, add_zero]`.

And remember `rw` also does `rfl`, you can replace the whole proof with `rw [add_succ, add_zero]`.

### Examining proofs

You might want to review this proof now; at three lines long it is your current record.
Don't worry there are much longer proofs, in fact, the
[Liquid Tensor Experiment](https://xenaproject.wordpress.com/2022/09/12/beyond-the-liquid-tensor-experiment/)
contains 90,000 lines of Lean proofs! For this reason Lean is a real programming language
with support for abstraction and extension so that you can get as much reusability as
possible in your Lean code.

The easiest way to see how the proof goal state progresses is to place your cursor at the
beginning of each line using the Up/Down arrow key to move down the proof and see the effect
of the previous line on the goal shown in the InfoView.

### Next

You have finished tutorial world! When you're happy, please move onto [Addition
World](../AdditionWorld.lean.md), and learn about proof by induction.

### Troubleshooting

**Question**: why has the InfoView gone blank?

**Answer**: try placing the cursor at different places in the file, the InfoView shows the
context at the cursor location.  If the InfoView is not updating at all no matter what you
do then there might be a problem with your VS Code setup.
See the [Quick
Start](https://leanprover.github.io/lean4/doc/quickstart.html) for more information.


-/