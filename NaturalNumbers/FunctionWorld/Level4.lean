import MyNat.Definition
namespace MyNat
open MyNat

/-!
# Function World

## Level 4: the `apply` tactic.

Let's do the same level again a different way:

![diagram](../assets/function_diag.svg)

We are given `p  ∈ P` and our goal is to find an element of `U`, or
in other words to find a path through the maze that links `P` to `U`.
In level 3 we solved this by using `have`s to move forward, from `P`
to `Q` to `T` to `U`.
Using the [apply tactic](../Tactics/apply.lean.md) we can instead construct
the path backwards, moving from `U` to `T` to `Q` to `P`.

Our goal is to construct an element of the set `U`. But `l:T → U` is
a function, so it would suffice to construct an element of `T`. Tell
Lean this by starting the proof below with

`apply l`

and notice that our assumptions don't change but *the goal changes*
from `⊢ U` to `⊢ T`.

Keep `apply`ing functions until your goal is `P`, and try not
to get lost! Now solve this goal
with `exact p`. Note: you will need to learn the difference between
`exact p` (which works) and `exact P` (which doesn't, because `P` is
not an element of  `P`).

## Definition
Given an element of `P` we can define an element of `U`.
-/
example (P Q R S T U: Type)
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