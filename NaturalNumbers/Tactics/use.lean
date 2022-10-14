import MyNat.Definition
/-!
# Tactic use

## Summary

`use` works on the goal. If your goal is `⊢ ∃ c : MyNat, 1 + x = x + c`
then `use 1` will turn the goal into `⊢ 1 + x = x + 1`, and the rather
more unwise `use 0` will turn it into the impossible-to-prove
`⊢ 1 + x = x + 0`.

## Details

`use` is a tactic which works on goals of the form `⊢ ∃ c, P(c)` where
`P(c)` is some proposition which depends on `c`. With a goal of this
form, `use 0` will turn the goal into `⊢ P(0)`, `use x + y` (assuming
`x` and `y` are natural numbers in your local context) will turn
the goal into `P(x + y)` and so on.



-/