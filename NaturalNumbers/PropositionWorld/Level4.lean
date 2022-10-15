import MyNat.Definition
namespace MyNat
open MyNat
/-!

# Proposition World

## Level 4: `apply`

Let's do the same level again a different way:

![diagram](../assets/propositions_diag.svg)

We are given a proof `p` of `P` and our goal is to find a proof of `U`, or
in other words to find a path through the maze that links `P` to `U`.
In level 3 we solved this by using `have`s to move forward, from `P`
to `Q` to `T` to `U`. Using the `apply` tactic we can instead construct
the path backwards, moving from `U` to `T` to `Q` to `P`.

Our goal is to prove `U`. But `l:T ⟹ U` is
an implication which we are assuming, so it would suffice to prove `T`.
Tell Lean this by starting the proof below with

`apply l`

and notice that our assumptions don't change but *the goal changes*
from `⊢ U` to `⊢ T`.

Keep `apply`ing implications until your goal is `P`, and try not
to get lost! Now solve this goal
with `exact p`. Note: you will need to learn the difference between
`exact p` (which works) and `exact P` (which doesn't, because `P` is
not a proof of `P`).

## Lemma : maze₂
We can solve a maze.
-/
lemma maze₂ (P Q R S T U: Prop)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U := by
  apply l
  apply j
  apply h
  exact p

/-!
Next up [Level 5](./Level5.lean.md).
-/