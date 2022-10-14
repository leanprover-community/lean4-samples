import MyNat.Definition
/-!
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
-/