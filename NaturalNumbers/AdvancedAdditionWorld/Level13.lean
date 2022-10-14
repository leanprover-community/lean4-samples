import MyNat.Definition
import MyNat.Addition
import AdvancedAdditionWorld.Level1 -- succ_inj
import AdvancedAdditionWorld.Level10 -- zero_ne_succ
namespace MyNat
open MyNat

/-!

# Advanced Addition World

## Level 13: `ne_succ_self`

The last level in Advanced Addition World is the statement
that `n ≠ succ n`.

## Lemma
For any natural number `n`, we have ` n ≠ succ n`.
-/
lemma ne_succ_self (n : MyNat) : n ≠ succ n := by
  induction n with
  | zero =>
    apply zero_ne_succ
  | succ n ih =>
    intro hs
    apply ih
    apply succ_inj
    assumption

/-!
Well that's a wrap on Advanced Addition World !

You can now move on to Advanced Multiplication World
(after first doing [Multiplication World](../MultiplicationWorld.lean.md), if you didn't do it already).
-/