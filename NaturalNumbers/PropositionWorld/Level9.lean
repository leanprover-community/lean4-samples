import MyNat.Definition
namespace MyNat
open MyNat
/-!
# Proposition world.

## Level 9: a big maze.

Hint: Lean's "congruence closure" tactic `cc` is good at mazes. You might want to try it now.
Perhaps I should have mentioned it earlier.

## Lemma
There is a way through the following maze.
-/
example (A B C D E F G H I J K L : Prop)
(f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
(f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
(f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
 : A → L := by
  intro a
  apply f15
  apply f11
  apply f9
  apply f8
  apply f5
  apply f2
  apply f1
  assumption

-- BUGBUG: NNG uses cc which is missing in lean4...

/-!
Now move onto [advanced proposition world](../AdvancedPropositionWorld.lean.md), where you will see
how to prove goals such as `P ∧ Q` (`P` and `Q`), `P ∨ Q` (`P` or `Q`),
`P ↔ Q` (`P ⟺ Q`).
You will need to learn five more tactics: `split`, `cases`,
`left`, `right`, and `exfalso`,
but they are all straightforward, and furthermore they are
essentially the last tactics you
need to learn in order to complete all the levels of this tutorial,
including all the 17 levels of [Inequality World](../InequalityWorld.lean.md).
-/

/-!
Next up [advanced proposition world](../AdvancedPropositionWorld.lean.md).
-/