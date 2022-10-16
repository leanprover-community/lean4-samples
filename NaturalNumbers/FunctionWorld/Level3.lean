import MyNat.Definition
namespace MyNat
open MyNat

/-!
# Function World

## Level 3: the `have` tactic

Say you have a whole bunch of sets and functions between them,
and your goal is to build a certain element of a certain set.
If it helps, you can build intermediate elements of other sets
along the way, using the [have tactic](../Tactics/have.lean.md). `have` is the Lean analogue
of saying "let's define an element `q ∈ Q` by..." in the middle of a calculation.
It is often not logically necessary, but on the other hand
it is very convenient, for example it can save on notation, or
it can break proofs or calculations up into smaller steps.

In this level, we have an element of `P` and we want an element
of `U`; during the proof we will make several intermediate elements
of some of the other sets involved. The diagram of sets and
functions looks like this pictorially:

![diagram](../assets/function_diag.svg)

and so it's clear how to make the element of `U` from the element of `P`.
Indeed, we could solve this level in one move by typing

`exact l (j (h p))`

But let us instead stroll more lazily through the level.
We can start by using the `have` tactic to make an element of `Q`:

`have q := h p`

and then we note that `j q` is an element of `T`

`have t : T := j q`

Notice how on this occasion we explicitly told Lean what set we thought `t` was in, with
that `: T` thing before the `:=`. We could even define `u` to be `l t`:

`have u : U := l t`

and then finish the level with `exact u`.

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
  have q := h p
  have t : T := j q
  have u : U := l t
  exact u

/-!
Remember you can move your cursor around with the arrow keys and explore the various tactic states
in this proof in Visual Studio Code, and note that the tactic state at the beginning of `exact u` is
this mess:

```
P Q R S T U : Type
p : P
h : P → Q
i : Q → R
j : Q → T
k : S → T
l : T → U
q : Q
t : T
u : U
⊢ U
```

It was already bad enough to start with, and we added three more
terms to it. In level 4 we will learn about the `apply` tactic
which solves the level using another technique, without leaving
so much junk behind.

Next up [Level 4](./Level4.lean.md).
-/