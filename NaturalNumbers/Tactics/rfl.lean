import MyNat.Definition
/-!
# Tactic `rfl`

`rfl` stands for "reflexivity", which is a fancy way of saying that it will prove any
goal of the form `A = A`. It doesn't matter how complicated `A` is.

This is supposed to be an extensible tactic
and users can add their own support for new reflexive relations.


-/
