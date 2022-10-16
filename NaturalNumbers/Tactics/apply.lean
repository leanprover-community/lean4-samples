import MyNat.Definition
/-!
# Tactic `apply`

`apply e` tries to match the current goal against the conclusion of `e`'s type.
If it succeeds, then the tactic returns as many subgoals as the number of premises that
have not been fixed by type inference or type class resolution.
Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution,
and first-order unification with dependent types.

For example, suppose you have the goal `⊢ Q` and you have the hypothesis
`g : P → Q` then `apply h` will construct the path backwards,
moving the goal from `Q` to `P`.


-/