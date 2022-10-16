import MyNat.Definition
/-!
# Tactics `left` and `right`

The tactics `left` and `right` work on a goal which is a type with two constructors, the classic example
being `P ∨ Q`. To prove `P ∨ Q` it suffices to either prove `P` or prove `Q`, and once you know which one
you are going for you can change the goal with left or right to the appropriate choice.

If `⊢ P ∨ Q` is your goal, then `left` changes this goal to `⊢ P`, and `right` changes it to `⊢ Q`.

-/