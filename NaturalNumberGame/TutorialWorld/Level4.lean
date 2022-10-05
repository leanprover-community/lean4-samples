import MyNat.Addition
open MyNat
/-!

# Tutorial world

## Level 4: addition

We have a new import -- the definition of addition.

Peano defined addition `a + b` by induction on `b`, or, more precisely, by recursion on `b`. He first
explained how to add 0 to a number: this is the base case.

- `add_zero (a : MyNat) : a + 0 = a`

We will call this theorem `add_zero`. More precisely, `add_zero` is the name of the _proof_ of the
theorem. Note the name of this proof. Mathematicians sometimes call it "Lemma 2.1" or "Hypothesis
P6" or something. But computer scientists call it `add_zero` because it tells you what the answer to
"x add zero" is. It's a much better name than "Lemma 2.1". Even better, we can use the rewrite tactic
with `add_zero`. If you ever see `x + 0` in your goal, `rw [add_zero]` should simplify it to `x`. This is
because `add_zero` is a proof that `x + 0 = x` (more precisely, `add_zero x` is a proof that `x + 0 = x` but
Lean can figure out the `x` from the context).

Now here's the inductive step. If you know how to add `d` to `a`, then Peano tells you how to add
`succ(d)` to `a`. It looks like this:

- `add_succ (a d : MyNat) : a + (succ d) = succ (a + d)`

What's going on here is that we assume `a + d` is already defined, and we define `a + (succ d)` to
be the number after it. Note the name of this proof too -- `add_succ` tells you how to add a successor
to something. If you ever see `... + succ ...` in your goal, you should be able to use `rw [add_succ]`, to
make progress. Here is a simple example where we shall see both. Let's prove that `x` plus the number
after 0 is the number after x.

Delete `sorry. Observe that the goal mentions `... + succ ...`. So type

`rw [add_succ]`

and hit enter; see the goal change. Do you see that the goal now mentions ... + 0 ...? So this
matches the `add_zero` theorem so you can add the following:

`rw [add_zero]`

and then observe that the proof is now complete: "Goals accomplished 🎉".
Note that because `rw` takes a list, you can also write the above two lines in one
using `rw [add_succ, add_zero]`.

**Lemma**`

For all natural numbers `a`, we have `a + (succ 0`) = succ a`.
-/
lemma add_succ_zero (a : MyNat) : a + (succ 0) = succ a := by
  sorry

/-!
### Examining proofs.

You might want to review this proof now; at three lines long it is our current record. Click on a
line in the proof and use the L/R arrow keys to put your cursor as far left as it will go. Then use
the U/D arrow keys to move your cursor up and down from line to line, and you can see what Lean is
thinking on each line of the proof.

### Next

You have finished tutorial world! When you're happy, let's move onto [Addition
World](../AdditionWorld/Level1.lean), and learn about proof by induction.

### Troubleshooting

**Question**: why has the InfoView gone blank?

**Answer**: try placing the cursor at different places in the file, the InfoView shows the
context at the cursor location.  If the InfoView is not updating at all no matter what you
do then there might be a problem with your VS Code setup.
See the [Quick
Start](https://leanprover.github.io/lean4/doc/quickstart.html) for more information.


-/