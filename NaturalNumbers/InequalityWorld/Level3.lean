import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import AdditionWorld.Level4 -- add_comm
namespace MyNat
open MyNat
/-!

# Inequality World

## Level 3: `le_succ_of_le`

We have seen how the `use` tactic makes progress on goals of the form `⊢ ∃ c, ...`.
But what do we do when we have a *hypothesis* of the form `h : ∃ c, ...`?
The hypothesis claims that there exists some natural number `c` with some
property. How are we going to get to that natural number `c`? It turns out
that the `cases` tactic can be used (just like it was used to extract
information from `∧` and `∨` and `↔` hypotheses). Let me talk you through
the proof of `a ≤ b ⟹ a ≤ succ b`.

The goal is an implication so we clearly want to start with

`intro h`

After this, if you *want*, you can do something like

`rw [le_iff_exists_add] at h ⊢ `

(get the sideways T with `\|-` or `\goal` then space). This `rw` changes the `≤` into
its `∃` form in `h` and the goal -- but if you are happy with just
*imagining* the `∃` whenever you read a `≤` then you don't need to do this line.

Our hypothesis `h` is now `∃ (c : MyNat), b = a + c` (or `a ≤ b` if you
elected not to do the definitional rewriting) so

`cases h with | _ c hc => ..`

gives you the natural number `c` and the hypothesis `hc : b = a + c`.
Now use `use` wisely and you're home.

## Lemma: `le_succ`
For all naturals `a` and `b`, if `a ≤ b` then `a ≤ succ b`.
-/
theorem le_succ (a b : MyNat) : a ≤ b → a ≤ (succ b) := by
  intro h
  cases h with
  | _ c hc => -- a = 0, b = 0
    rw [hc]
    use c + 1

/-!

You can use `succ c` or `c + 1` or `1 + c`. Those numbers are all
equal, right? Try these variations and see what happens.

Now what about if you do `use 1 + c`? Can you work out
what is going on? Does it help if I tell you that the *definition*
of `1` is `succ 0`?

Next up [Level 4](./Level4.lean.md).
-/
