import MyNat.Definition
/-!

## Tactic : tauto

## Summary

The `tauto` tactic (and its variant `tauto!`) will close various logic
goals.

## Details

`tauto` is an all-purpose logic tactic which will try to solve goals using pure
logical reasoning -- for example it will close the following goal:

```
P Q : Prop
hP : P
hQ : Q
⊢ P ∧ Q
```

`tauto` is supposed to only use constructive logic, but its big brother `tauto!` uses classical logic
and hence closes more goals.

-/