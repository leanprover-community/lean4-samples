import MyNat.Definition
/-!
# Tactic `constructor`

If the main goal's target type is an inductive type, `constructor` solves it with
the first matching constructor, or else fails.

For example, if the goal is `⊢ P ∧ Q` then it finds the matching constructor `And.intro`
which has 2 parameters, so it solves the goal with two sub-goals, namely `⊢ P` and `⊢ Q`.


-/