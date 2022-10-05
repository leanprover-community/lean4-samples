import MyNat.Definition -- Imports the natural numbers.
import MyNat.Addition -- imports addition.
open MyNat

/-
# Addition World.

Welcome to Addition World. If you've done all four levels in [Tutorial World](../TutorialWorld/Level1.lean)
and know about `rw` and `rfl`, then you're in the right place. Here's
a reminder of the things you're now equipped with which we'll need in this world.

## Data:

  * a type called `MyNat`
  * a term `(0 : MyNat)`, interpreted as the number zero.
  * a function `succ : MyNat → MyNat`, with `succ n` interpreted as "the number after `n`".
  * Usual numerical notation 0,1,2 etc (although 2 onwards will be of no use to us until much later ;-) ).
  * Addition (with notation `a + b`).

## Theorems:

  * `add_zero (a : MyNat) : a + 0 = a`. Use with `rw [add_zero]`.
  * `add_succ (a b : MyNat) : a + succ(b) = succ(a + b)`. Use with `rw [add_succ]`.
  * The principle of mathematical induction. Use with `induction` (see below)


## Tactics:

  * `rfl` :  proves goals of the form `X = X`
  * `rw [h]` : if h is a proof of `A = B`, changes all A's in the goal to B's.
  * `induction n with ...` : we're going to learn this right now.

# Important thing:

This is a *really* good time to check you can get "mouse hover help on anything in the Lean program.
If you hover over 'rfl' you get information on that tactic.  You can also press F12 to jump
right into the definition of all the helpers functions we use here.

## Level 1: the `induction` tactic.

OK so let's see induction in action. We're going to prove

  `zero_add (n : MyNat) : 0 + n = n`.

That is: for all natural numbers `n`, `0+n=n`. Wait - what is going on here? Didn't we already prove
that adding zero to `n` gave us `n`? No we didn't! We proved `n + 0 = n`, and that proof was called
`add_zero`. We're now trying to establish `zero_add`, the proof that `0 + n = n`. But aren't these
two theorems the same? No they're not! It is *true* that `x + y = y + x`, but we haven't *proved* it
yet, and in fact we will need both `add_zero` and `zero_add` in order to prove this. In fact
`x + y = y + x` is the boss level for addition world, and `induction` is the only other tactic you'll
need to beat it.

Now `add_zero` is one of Peano's axioms, so we don't need to prove it, we already have it (indeed,
if you've used Goto Definition (F12) on this theorem you can even see it). To prove `0 + n = n` we
need to use induction on `n`. While we're here, note that `zero_add` is about zero add something,
and `add_zero` is about something add zero. The names of the proofs tell you what the theorems are.
Anyway, let's prove `0 + n = n`.

Delete `sorry` and replace it with  the following:
```lean
  induction n with
  | zero => ...
  | succ n ih => ...
```

Notice that the induction tactic has create *two sub-goals*! The
induction tactic has generated for us a base case with `n = 0` (the goal at the top)
and an inductive step (the goal underneath). The golden rule: **Tactics operate on the first goal**
- the goal at the top. So let's just worry about that top goal now, the base case.
If you place the cursor right after the `=>` symbol you will see the goal listed in
the InfoView as `⊢ 0 + zero = zero`.

Remember that `add_zero` (the proof we have already) is the proof of `x + 0 = x`
(for any `x`) so we can try

`rw [add_zero]`

What do you think the goal will change to? Remember to just keep focussing on the top goal, ignore
the other one for now, it's not changing and in fact, the InfoView tells you why:
```
tactic 'rewrite' failed, did not find instance of the pattern in the target expression
```

But you should be able to solve the top goal yourself by replacing the `rw` with a simple `rfl`. You
should now see `Goals accomplished 🎉` when your cursor is placed on the right of the `rfl` which
means you have solved this base case sub-goal, we are now be back down to one goal -- the inductive
step. Take a look at the text below the lemma to see an explanation of this goal.

**Lemma**

For all natural numbers `n`, we have
``0 + n = n.``
-/
lemma zero_add (n : MyNat) : zero + n = n := by
  sorry

/-
We're in the successor case, and the InfoView tactic state should look
something like this:

```
case succ
n: MyNat
ih: 0 + n = n
⊢ 0 + succ n = succ n
```

*Important:* make sure that you only have one goal at this point. You should have proved `0 + 0 = 0`
by now. Tactics only operate on the top goal.

The first line just reminds us we're doing the inductive step. We have a fixed natural number `n`,
and the inductive hypothesis `ih : 0 + n = n` which means this hypothesis proves of `0 + n = n`. Our
goal is to prove `0 + succ n = succ n`. In other words, we're showing that if the lemma is true for
`n`, then it's also true for `n + 1`. That's the inductive step that you might be familiar with in
proof by induction. Once we've proved this inductive step, we will have proved `zero_add` by the
principle of mathematical induction.

To prove our goal, we need to use `add_succ`. We know that `add_succ 0 d`
is the result that `0 + succ d = succ (0 + d)`, so the first thing
we need to do is to replace the left hand side `0 + succ d` of our
goal with the right hand side. We do this with the `rw` command. You can write

`rw [add_succ]`

(or even `rw add_succ 0 n,` if you want to give Lean all the inputs instead of making it
figure them out itself). The goal should change to

`⊢ succ (0 + n) = succ n`

Now remember our inductive hypothesis `ih : 0 + d = d`. We need
to rewrite this too! Type

`rw [ih]`

(don't forget the comma). The goal will now change to

`⊢ succ d = succ d`

and the `rw` tactic will automatically finish our proof using the `rfl` tactic.
After you apply it, Lean will inform you that there are no goals left. You are done!

Remember that you can write `rw [add_succ, ih]` also, but notice that rewriting is
order dependent and that `rw [ih, add_succ]` does not work.

## Now venture off on your own.

Those three tactics --

* `induction n with ...`
* `rw [h]`
* `rfl`

will get you quite a long way through this game. Using only these tactics
you can beat Addition World level 4 (the boss level of Addition World),
all of Multiplication World including the boss level `a * b = b * a`,
and even all of Power World including the fiendish final boss. This route will
give you a good grounding in these three basic tactics; after that, if you
are still interested, there are other worlds to master, where you can learn
more tactics.

But we're getting ahead of ourselves, you still have to beat the rest of Addition World.
We're going to stop explaining stuff carefully now. If you get stuck or want
to know more about Lean (e.g. how to do much harder maths in Lean),
ask in `#new members` at [the Lean chat](https://leanprover.zulipchat.com).
(login required, real name preferred, github account id is handy).
Kevin or Mohammad or one of the other people there might be able to help.

Good luck! Click on [next level](./Level2.lean) to solve some levels on your own.

-/
