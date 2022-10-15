import MyNat.Definition
namespace MyNat
open MyNat
/-!
# Proposition World

## Level 3: `have`

Say you have a whole bunch of propositions and implications between them, and your goal is to build
a certain proof of a certain proposition. If it helps, you can build intermediate proofs of other
propositions along the way, using the `have` command. `have q : Q := ...` is the Lean analogue of
saying "We now see that we can prove `Q`, because..." in the middle of a proof. It is often not
logically necessary, but on the other hand it is very convenient, for example it can save on
notation, or it can break proofs up into smaller steps.

In the level below, we have a proof of `P` and we want a proof of `U`; during the proof we will
construct proofs of of some of the other propositions involved. The diagram of propositions and
implications looks like this pictorially:

![diagram](../assets/propositions_diag.svg)

and so it's clear how to deduce `U` from `P`.
Indeed, we could solve this level in one move by typing

`exact l (j (h p))`

But let us instead stroll more lazily through the level.
We can start by using the `have` tactic to make a proof of `Q`:

`have q := h p`

and then we note that `j q` is a proof of `T`:

`have t : T := j q`

(note how we explicitly told Lean what proposition we thought `t` was
a proof of, with that `: T` thing before the `:=`)
and we could even define `u` to be `l t`:

`have u : U := l t`

and then finish the level with

`exact u`

## Lemma : maze

In the maze of logical implications above, if `P` is true then so is `U`.
-/
lemma maze (P Q R S T U: Prop)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U := by
  have q := h p
  have t := j q
  have u := l t
  exact u

/-!
Remember you can move your cursor around with the arrow keys and explore the various tactic states
in this proof in Visual Studio Code, and note that the tactic state at the beginning of `exact u` is
this mess:

```
P Q R S T U : Prop
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

It was already bad enough to start with, and we added three more terms to it. In level 4 we will
learn about the `apply` tactic which solves the level using another technique, without leaving so
much junk behind.

Next up [Level 4](./Level4.lean.md).
-/