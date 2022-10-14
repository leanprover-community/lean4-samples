import MyNat.Definition
/-!
# Tactics

## [rfl](./Tactics/rfl.lean.md)

`rfl` stands for "reflexivity", which is a fancy way of saying that it will prove any
goal of the form A = A. It doesn't matter how complicated A is.

## [rewrite](./Tactics/rewrite.lean.md)

The `rewrite` tactic is the way to "substitute in" the value of a variable. In general, if you have a
hypothesis of the form `A = B`, and your goal mentions the left hand side `A` somewhere, then the
`rewrite` tactic will replace the `A` in your goal with a `B`.

## [rw](./Tactics/rw.lean.md)

The `rw` tactic is simply `rewrite` followed by `rfl`.

## [induction](./Tactics/induction.lean.md)

The `induction` tactic applies induction on inductive type to the main goal,
producing one goal for each constructor of the inductive type.

## [simp](./Tactics/simp.lean.md)

The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or
non-dependent hypotheses.

## [exact](./Tactics/exact.lean.md)

If you can explicitly see how to make an element of your goal set,
i.e. you have a formula for it, then you can just write `exact <formula>`
and this will close the goal.


## [intro](./Tactics/intro.lean.md)

If your goal is `⊢ P → Q` then `intro p` will introduce a new
hypothesis `p : P` and change the goal to `⊢ Q`.


## [intros](./Tactics/intros.lean.md)

The `intros` tactic is like `intro` only it can introduce multiple hypotheses at once.

## [have](./Tactics/have.lean.md)

`have h : t := e` adds the hypothesis `h : t` to the current goal if `e` is a term
of type `t`.

## [apply](./Tactics/apply.lean.md)

`apply e` tries to match the current goal against the conclusion of `e`'s type.

## [assumption](./Tactics/assumption.lean.md)

The `assumption` tries to solve the goal using a
hypothesis of compatible type

## [constructor](./Tactics/constructor.lean.md)

The `constructor` tactic tries to solve the goal using a
hypothesis of compatible type.

## [cases](./Tactics/cases.lean.md)

Assuming `x` is a variable in the local context with an inductive type,
`cases x` splits the main goal, producing one goal for each constructor of the
inductive type, in which the target is replaced by a general instance of that constructor.

## [left/right](./Tactics/leftright.lean.md)

If `⊢ P ∨ Q` is your goal, then `left` changes this goal to `⊢ P`, and `right` changes it to `⊢ Q`.

## [exfalso](./Tactics/exfalso.lean.md)

`exfalso` converts a goal `⊢ tgt` into `⊢ False` by applying `False.elim`.

## [contradiction](./Tactics/contradiction.lean.md)

The `contradiction` tactic closes the main goal if its hypotheses
are "trivially contradictory".

## [by_cases](./Tactics/by_cases.lean.md)

`by_cases h : P` does a cases split on whether `P` is true or false.

## [use](./Tactics/use.lean.md)

`use` is a tactic which works on goals of the form `⊢ ∃ c, P(c)` where
`P(c)` is some proposition which depends on `c`. You can specify one of
the values of `c` that you would like to choose to proof thereby proving
the existance is true.

## [revert](./Tactics/revert.lean.md)

`revert x` is the opposite to `intro x`.

## [tauto](./Tactics/tauto.lean.md)

The `tauto` tactic (and its variant `tauto!`) will close various logic
goals.

## [<;>](./Tactics/concatenate.lean.md)

`tac1 <;> tac2` runs `tac1` on the main goal and `tac2` on each produced goal,
concatenating all goals produced by `tac2`.

-/