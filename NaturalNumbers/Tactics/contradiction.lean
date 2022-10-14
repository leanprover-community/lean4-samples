import MyNat.Definition
/-!
# Tactic contradiction

The `contradiction` tactic closes the main goal if its hypotheses
are "trivially contradictory".

Inductive type/family with no applicable constructors

- `example (h : False) : p := by contradiction`

Injectivity of constructors

- `example (h : none = some true) : p := by contradiction  --`

Decidable false proposition

- `example (h : 2 + 2 = 3) : p := by contradiction`

Contradictory hypotheses

  `example (h : p) (h' : ¬ p) : q := by contradiction`

Other simple contradictions such as

- `example (x : Nat) (h : x ≠ x) : p := by contradiction`

-/