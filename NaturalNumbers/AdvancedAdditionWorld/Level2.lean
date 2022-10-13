import MyNat.Definition
import MyNat.Addition
import AdvancedAdditionWorld.Level1 -- succ_inj
namespace MyNat
open MyNat
/-!

# Advanced Addition World

## Level 2: `succ_succ_inj`

In the below theorem, we need to apply `succ_inj` twice. Once to prove
`succ (succ a) = succ (succ b) ⟹ succ a = succ b`, and then again to prove `succ a = succ b ⟹ a = b`.
However `succ a = succ b` is nowhere to be found, it's neither an assumption or a goal when we start
this level. You can make it with `have` or you can use `apply`.

## Theorem : succ_succ_inj

For all naturals `a` and `b`, if we assume `succ (succ a) = succ (succ b)`, then we can
deduce `a = b`.
-/
theorem succ_succ_inj {a b : MyNat} (h : succ (succ a) = succ (succ b)) :  a = b := by
  apply succ_inj
  apply succ_inj
  exact h

/-!
## Other solutions

Make sure you understand them all. And remember that `rw` should not be used
with `succ_inj` -- `rw` works only with equalities or `↔` statements,
not implications or functions.

-/

example {a b : MyNat} (h : succ (succ a) = succ (succ b)) :  a = b := by
  apply succ_inj
  exact succ_inj h

example {a b : MyNat} (h : succ (succ a) = succ (succ b)) :  a = b := by
  exact succ_inj (succ_inj h)

/-!
Next up [Level 3](./Level3.lean.md)
-/
