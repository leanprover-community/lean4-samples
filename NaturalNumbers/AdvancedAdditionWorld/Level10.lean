import MyNat.Definition
import MyNat.Addition
import AdvancedAdditionWorld.Level9 -- succ_ne_zero
namespace MyNat
open MyNat
/-!
# Advanced Addition World

## Level 10: `add_left_eq_zero`

## Important: the definition of `≠`

In Lean, `a ≠ b` is *defined to mean* `(a = b) → false`.
This means that if you see `a ≠ b` you can *literally treat
it as saying* `(a = b) → false`. Computer scientists would
say that these two terms are *definitionally equal*.

The following lemma, `a+b=0 ⟹ b=0`, will be useful in [Inequality World](../InequalityWorld.lean.md).
Let me go through the proof, because it introduces several new
concepts:

* `cases b`, where `b : MyNat`
* `exfalso`
* `apply succ_ne_zero`

We're going to prove `a+b=0 ⟹ b=0`. Here is the
strategy. Each natural number is either `0` or `succ d` for
some other natural number `d`. So we can start the proof
with

`cases b with d`

and then we have two goals, the case `b = 0` (which you can solve easily)
and the case `b = succ d`, which looks like this:

```
a d : MyNat,
h : a + succ d = 0
⊢ succ d = 0
```

Our goal is impossible to prove. However our hypothesis `h`
is also impossible, meaning that we still have a chance!
First let's see why `h` is impossible. We can

`rw [add_succ] at h`

to turn `h` into `h : succ (a + d) = 0`. Because
`succ_ne_zero (a + d)` is a proof that `succ (a + d) ≠ 0`,
it is also a proof of the implication `succ (a + d) = 0 → false`.
Hence `succ_ne_zero (a + d) h` is a proof of `false`!
Unfortunately our goal is not `false`, it's a generic
false statement.

Recall however that the `exfalso` command turns any goal into `false`
(it's logically OK because `false` implies every proposition, true or false).


## Lemma
If `a` and `b` are natural numbers such that `a + b = 0` then `b = 0`.
-/
lemma add_left_eq_zero {{a b : MyNat}} (h : a + b = 0) : b = 0 := by
  cases b with
  | zero =>
    rfl
  | succ d =>
    rw [add_succ] at h
    exfalso
    apply succ_ne_zero (a + d)
    exact h

/-!
Next up [Level 11](./Level11.lean.md)
-/
