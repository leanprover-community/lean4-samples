import MyNat.Definition
/-!
# Tactic `repeat`

`repeat x` applies tactic `x` to main goal. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.


-/
