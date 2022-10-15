import MyNat.Definition
import MyNat.Addition
import AdditionWorld.Level6
namespace MyNat
open MyNat

axiom succ_inj {a b : MyNat} : succ a = succ b → a = b

/-!

# Advanced Addition World

## Level 1: `succ_inj`. A function

Let's learn how to use `succ_inj`. You should know a couple of ways to prove the below -- one
directly using an `exact`, and one which uses an `apply` first. But either way you'll need to use
`succ_inj`.

## Theorem
For all naturals `a` and `b`, if we assume `succ a = succ b`, then we can
deduce `a = b`.
-/
theorem succ_inj' {a b : MyNat} (hs : succ a = succ b) :  a = b := by
  exact succ_inj hs

/-!
## Important thing.

You can rewrite proofs of *equalities*. If `h : A = B` then `rw [h]` changes `A`s to `B`s.
But you *cannot rewrite proofs of implications*. `rw [succ_inj]` will *never work*
because `succ_inj` isn't of the form `A = B`, it's of the form `A ⟹ B`. This is one
of the most common mistakes I see from beginners. `⟹` and `=` are *two different things*
and you need to be clear about which one you are using.

Next up [Level 2](./Level2.lean.md).
-/
