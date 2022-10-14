import MyNat.Definition
/-!
# Tactic assumption

The `assumption` tactic tries to solve the main goal using a hypothesis of compatible type, or else fails.
Note also the `‹t›` term notation, which is a shorthand for `show t by assumption`.


-/