import MyNat.Definition
namespace MyNat
open MyNat
/-!

# Proposition World

## Level 1: the `exact` tactic


The local context (or tactic state) at the beginning of
the example below looks like this:

```
P Q : Prop
p : P
h : P → Q
⊢ Q
```

In this situation, we have true/false statements `P` and `Q`,
a proof `p` of `P`, and `h` is the hypothesis that `P → Q` (P implies Q).
Our goal is to construct a proof of `Q`. It's clear what to do
*mathematically* to solve this goal, `P` is true and `P` implies `Q`
so `Q` is true. But how to do it in Lean?

Adopting a point of view wholly unfamiliar to many mathematicians,
Lean interprets the hypothesis `h` as a function from proofs
of `P` to proofs of `Q`, so the rather surprising approach

`exact h p`

works to close the goal!

Note that `exact h P` (with a capital P) won't work;
this is a common error by beginners. "We're trying to solve `P`
so it's exactly `P`". The goal states the *theorem*, your job is to
construct the *proof*. `P` is not a proof of `P`, it's `p` that is a proof of `P`.

The analogy would be like trying to call a function "sin X" with "Float" instead of a number 3.1415.

## Lemma

If `P` is true, and `P → Q` is also true, then `Q` is true.
-/
example (P Q : Prop) (p : P) (h : P → Q) : Q := by
  exact h p

/-!
Look familiar? The reason this works so elegantly is because the Lean programming language
has unified Propositions with the Type system of the language.

Next up [Level 2](./Level2.lean.md).
-/