import MyNat.Definition
namespace MyNat
open MyNat

/-!
# Function world.

## Level 9: a big maze.

In [Proposition World](../PropositionWorld.lean.md) you will see a variant of this example
which can be solved by a tactic. It would be an interesting project to make a tactic
which could automatically solve this sort of level in Lean.

You can of course work both forwards and backwards, or you could crack and draw a picture.

## Definition
Given a bunch of functions, we can define another one.
-/
example (A B C D E F G H I J K L : Type)
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


/-!
Here we finish this proof with a new tactic `assumption` instead of `exact a`.
The [`assumption` tactic](../Tactics/assumption.lean.md) tries to solve the goal using a
hypothesis of compatible type.  Since we have the hypothesis named `a` it finds
it and completes the proof.

That's the end of Function World! Next it's [Proposition World](../PropositionWorld.lean.md), and
the tactics you've learnt in Function World are enough to solve all nine levels! In fact, the levels
in [Proposition World](../PropositionWorld.lean.md) might look strangely familiar...
-/
