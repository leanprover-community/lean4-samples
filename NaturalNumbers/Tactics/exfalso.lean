import MyNat.Definition
/-!
# Tactic `exfalso`

## Summary

`exfalso` changes your goal to `False`.

## Details

We know that `False` implies `P` for any proposition `P`, and so if your goal is `P`
then you should be able to `apply` `False → P` and reduce your goal to `False`. This
is what the `exfalso` tactic does. The theorem that `False → P` is called `False.elim`
so one can achieve the same effect with `apply False.elim`.

You might think this is a step backwards, but if you have a hypothesis `h : ¬ P`
then after `rw [not_iff_imp_false] at h` you can `apply h` to make progress.

This tactic can also be used in a proof by contradiction, where the hypotheses are enough
to deduce a contradiction and the goal happens to be some random statement (possibly
a false one) which you just want to simplify to `False`.

-/