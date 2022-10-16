import MyNat.Definition
/-!
## Tactic `revert`

## Summary

`revert x` is the opposite to `intro x`.

## Details

If the tactic state looks like this

```
P Q : Prop
h : P
⊢ Q
```

then `revert h` will change it to

```
P Q : Prop
⊢ P → Q
```

`revert` also works with things like natural numbers: if
the tactic state looks like this

```
m : MyNat
⊢ m + 1 = succ m
```

then `revert m` will turn it into

```
⊢ ∀ (m : MyNat), m + 1 = MyNat.succ m
```
-/