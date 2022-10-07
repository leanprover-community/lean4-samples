import MyNat.Definition
namespace MyNat
open MyNat

/-!
# Function World

## Level 1: the `exact` tactic.

Given an element of `P` and a function from `P` to `Q`,
we define an element of `Q`.
-/
example (P Q : Type) (p : P) (h : P → Q) : Q := by
  exact h p

/-!
Note that `example` is just like a `theorem` or a `lemma`
except it has no name.

If you place your cursor at the end of the `example` line above
the tactic state will look like this:

```
P Q : Type,
p : P,
h : P → Q
⊢ Q
```

In this situation, we have sets `P` and `Q` (but Lean calls them types),
and an element `p` of `P` (written `p : P`
but meaning `p ∈ P`). We also have a function `h` from `P` to `Q`,
and our goal is to construct an
element of the set `Q`. It's clear what to do *mathematically* to solve
this goal -- we can
make an element of `Q` by applying the function `h` to
the element `p`. But how to do it in Lean? There are at least two ways
to explain this idea to Lean,
and here we will learn about one of them, namely the method which
uses the `exact` tactic.

## The `exact` tactic.

If you can explicitly see how to make an element of your goal set,
i.e. you have a formula for it, then you can just write `exact <formula>`
and this will close the goal.

So given that the function application `h p` is an element of `Q` so you can just write
`exact h p` to close the goal.

## Important note

Note that `exact h P` won't work (with a capital `P`);
this is a common error for beginners.
`P` is not an element of `P`, it's `p` that is an element of `P`.

## Summary

If the goal is `⊢ X` then `exact x` will close the goal if
and only if `x` is a term of type `X`.

## Details

Say `P`, `Q` and `R` are types (i.e., what a mathematician
might think of as either sets or propositions),
and the local context looks like this:

```
p : P,
h : P → Q,
j : Q → R
⊢ R
```

If you can spot how to make a term of type `R`, then you
can just make it and say you're done using the `exact` tactic
together with the formula you have spotted. For example the
above goal could be solved with

`exact j (h p)`

because `j (h p)` is easily checked to be a term of type `R`
(i.e., an element of the set `R`, or a proof of the proposition `R`).


Next up [Level 2](./Level2.lean.md)
-/