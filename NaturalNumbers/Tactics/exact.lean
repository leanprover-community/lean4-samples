import MyNat.Definition
/-!
# Tactic `exact`

`exact e` closes the main goal if its target type matches that of `e`.

This is essentially a short hand for:

```lean
have h2 := e
assumption
```

-/