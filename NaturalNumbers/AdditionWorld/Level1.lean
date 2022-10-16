import MyNat.Addition -- imports addition.
namespace MyNat
open MyNat

/-!
# Addition World

## Level 1: the `induction` tactic

OK so let's see induction in action. We're going to prove

  `zero_add (n : MyNat) : 0 + n = n`.

That is: for all natural numbers `n`, `0+n=n`. Wait - what is going on here? Didn't you already prove
that adding zero to `n` gave us `n`? No you didn't! You proved `n + 0 = n`, and that proof was called
`add_zero`. We're now trying to establish `zero_add`, the proof that `0 + n = n`. But aren't these
two theorems the same? No they're not! It is *true* that `x + y = y + x`, but you haven't *proved* it
yet, and in fact you will need both `add_zero` and `zero_add` in order to prove this. In fact
`x + y = y + x` is the boss level for addition world, and `induction` is the only other tactic you'll
need to beat it.

Now `add_zero` is one of Peano's axioms, so you don't need to prove it, you already have it (indeed,
if you've used Goto Definition (F12) on this theorem you can even see it). To prove `0 + n = n` we
need to use induction on `n`. While we're here, note that `zero_add` is about zero add something,
and `add_zero` is about something add zero. The names of the proofs tell you what the theorems are.

## Lemma

For all natural numbers `n`, we have `0 + n = n`.
-/
lemma zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [add_succ]
      rw [ih]

/-!

Notice that the [induction tactic](../Tactics/induction.lean.md) has created *two sub-goals*
which you can match using vertical bar pattern patching.

The induction tactic has generated for us a base case with `n = zero` (the goal at the top)
and an inductive step (the goal underneath). The golden rule: **Tactics operate on the first goal**.
- The goal at the top. So let's just worry about that top goal now, the base case.
If you place the cursor right after the `=>` symbol you will see the goal listed in
the InfoView as `⊢ 0 + zero = zero`.

Remember that `add_zero` (the proof we have already) is the proof of `x + 0 = x`
(for any `x`) so you can try `rw [add_zero]` here but what do you think the goal will change to?
Remember to just keep focussing on the top goal, ignore
the other one for now, it's not changing and in fact, the InfoView tells you why:
```
tactic 'rewrite' failed, did not find instance of the pattern in the target expression
```

But as you can see `rfl` can solve the first case. You should now see `Goals accomplished 🎉` when
your cursor is placed on the right of the `rfl` which means you have solved this base case sub-goal,
and you are ready to tackle the next sub-goal -- the inductive step. Take a look at the text below
the lemma to see an explanation of this goal.

In the successor case the InfoView tactic state should look something like this:

```
case succ
n: MyNat
ih: 0 + n = n
⊢ 0 + succ n = succ n
```

*Important:* make sure that you only have one goal at this point. You should have proved `0 + 0 = 0`
by now. Tactics only operate on the top goal.

The first line just reminds you you're doing the inductive step. You have a fixed natural number `n`,
and the inductive hypothesis `ih : 0 + n = n` which means this hypothesis proves `0 + n = n`. Your
goal is to prove `0 + succ n = succ n`. In other words, we're showing that if the lemma is true for
`n`, then it's also true for `n + 1`. That's the inductive step that you might be familiar with in
proof by induction. Once we've proved this inductive step, you will have proved `zero_add` by the
principle of mathematical induction.

To prove your goal, you need to use `add_succ` which you proved in
[Tutorial World Level 4](../TutorialWorld/Level4.lean.md). Note that `add_succ 0 d`
is the result that `0 + succ d = succ (0 + d)`, so the first thing
you need to do is to replace the left hand side `0 + succ d` of your
goal with the right hand side. You do this with the `rw` command: `rw [add_succ]`
(or even `rw [add_succ 0 n]` if you want to give Lean all the inputs instead of making it
figure them out itself). Notice goal changes to `⊢ succ (0 + n) = succ n`.

Now remember the inductive hypothesis `ih : 0 + d = d`. This `0 + d` matches
the `(0 + n)` in the goal, so you can write that using `rw [ih]`.
The goal will now change to

`⊢ succ d = succ d`

and the `rw` tactic will automatically finish our proof using the `rfl` tactic.
After you apply it, Lean will inform you that there are no goals left. You are done!

Remember that you can write `rw [add_succ, ih]` also, but notice that rewriting is
order dependent and that `rw [ih, add_succ]` does not work.

## Now venture off on your own

Those three tactics --

* `induction n with ...`
* `rw [h]`
* `rfl`

will get you quite a long way through this tutorial. Using only these tactics
do all of Addition World,
all of [Multiplication World](../MultiplicationWorld.lean.md) including the boss level `a * b = b * a`,
and even all of [Power World](../PowerWorld.lean.md) including the fiendish final boss. This route will
give you a good grounding in these three basic tactics; after that, if you
are still interested, there are other worlds to master, where you can learn
more tactics.

But we're getting ahead of ourselves, you still have to read the rest of Addition World.
We're going to stop explaining stuff carefully now. If you get stuck or want
to know more about Lean (e.g. how to do much harder maths in Lean),
ask in `#new members` at [the Lean chat](https://leanprover.zulipchat.com).
(login required, real name preferred, github account id is handy).
Kevin or Mohammad or one of the other people there might be able to help.

On to [level 2](./Level2.lean.md).

-/
