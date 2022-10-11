import MyNat.Definition
namespace MyNat
open MyNat
/-!
# Advanced proposition world.

## Level 10: the law of the excluded middle.

We proved earlier that `(P → Q) → (¬ Q → ¬ P)`. The converse,
that `(¬ Q → ¬ P) → (P → Q)` is certainly true, but trying to prove
it using what we've learnt so far is impossible (because it is not provable in
constructive logic). For example, after

```
intro h
intro p
repeat rw [not_iff_imp_false] at h
```

in the below, you are left with
```
P Q : Prop,
h : (Q → false) → P → false
p : P
⊢ Q
```

The tools you have are not sufficient to continue. But you can just prove this, and any other basic
lemmas of this form like `¬ ¬ P → P`, using the `by_cases` tactic. Here we start with the usual
`intros` to turn the implication into hypotheses `h : ¬ Q → ¬ P` and `p : P` which leaves with the
goal of `⊢ Q`.  But how can you prove `Q` using these hypotheses?  You can use this tactic:

`by_cases q : Q`

This creates two sub-goals `pos` and `neg` with the first one assuming Q is true - which can easily
satisfy the goal! and the second one assuming Q is false. But how can `h: ¬Q → ¬P`, `p: P`, `q: ¬Q`
prove the goal `⊢ Q` ? Well if you apply `q` to the hypothesis `h` you end up with the conclusion `¬
P`, but then you have a contradiction in your hypotheses saying `P` and `¬ P` which the
`contradiction` tactic can take care of that.

The `contradiction` tactic closes the main goal if its hypotheses
are "trivially contradictory".

## Lemma
If `P` and `Q` are true/false statements, then
`(¬ Q ⟹ ¬ P) ⟹ (P ⟹ Q).`
-/
lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by
  intro h
  intro p
  by_cases q : Q
  exact q
  have np := h q
  contradiction
/-!

Here's the Lean3 version:
```lean
lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) :=
begin
  by_cases p : P; by_cases q : Q,
  repeat {cc},
end
```
OK that's enough logic -- now perhaps it's time to go on to Advanced Addition World!
-/


/-!
## Pro tip

In fact the tactic `tauto!` just kills this goal (and many other logic goals) immediately.


## Tactic : by_cases

## Summary

`by_cases h : P` does a cases split on whether `P` is true or false.

## Details

Some logic goals cannot be proved with `intro` and `apply` and `exact`.
The simplest example is the law of the excluded middle `¬ ¬ P → P`.
You can prove this using truth tables but not with `intro`, `apply` etc.
To do a truth table proof, the tactic `by_cases h : P` will turn a goal of
`⊢ ¬ ¬ P → P` into two goals

```
P : Prop,
h : P
⊢ ¬¬P → P

P : Prop,
h : ¬P
⊢ ¬¬P → P
```

Each of these can now be proved using `intro`, `apply`, `exact` and `exfalso`.
Remember though that in these simple logic cases, high-powered logic
tactics like `cc` and `tauto!` will just prove everything.



## Tactic : tauto

## Summary

The `tauto` tactic (and its variant `tauto!`) will close various logic
goals.

## Details

`tauto` is an all-purpose logic tactic which will try to solve goals using pure
logical reasoning -- for example it will close the following goal:

```
P Q : Prop,
hP : P,
hQ : Q
⊢ P ∧ Q
```

`tauto` is supposed to only use constructive logic, but its big brother `tauto!` uses classical logic
and hence closes more goals.
-/
