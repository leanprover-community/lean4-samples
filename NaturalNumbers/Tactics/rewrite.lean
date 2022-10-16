import MyNat.Definition
/-!
# Tactic `rewrite`

The `rewrite` tactic is the way to "substitute in" the value of a variable. In general, if you have a
hypothesis of the form `A = B`, and your goal mentions the left hand side `A` somewhere, then the
`rewrite` tactic will replace the `A` in your goal with a `B`.

`rewrite` takes a list of hypotheses, and will try to apply each one in turn.
So `rewrite [e]` applies identity `e` as a rewrite rule to the target of the main goal.

You can also make rewrite apply the hypothesis in reverse direction by adding
a left arrow (`←` or `<-`) before the name of the hypothesis `rewrite [←e]`.

If `e` is a defined constant, then the equational theorems associated with `e` are used.
This provides a convenient way to unfold `e`.

`rewrite [e₁, ..., eₙ]` applies the given rules sequentially.

`rewrite [e] at l` rewrites e at location(s) l, where l is either `*` or a list of hypotheses in the
local context. In the latter case a turnstile, `⊢` or `|-`, can also be used to signify the target of the goal:
`rewrite [e] at l ⊢`

-/
