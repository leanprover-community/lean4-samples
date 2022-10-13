import AdvancedAdditionWorld.Level1
import AdvancedAdditionWorld.Level2
import AdvancedAdditionWorld.Level3
import AdvancedAdditionWorld.Level4
import AdvancedAdditionWorld.Level5
import AdvancedAdditionWorld.Level6
import AdvancedAdditionWorld.Level7
import AdvancedAdditionWorld.Level8
import AdvancedAdditionWorld.Level9
import AdvancedAdditionWorld.Level10
import AdvancedAdditionWorld.Level11
import AdvancedAdditionWorld.Level12
import AdvancedAdditionWorld.Level13
/-!
# Advanced Addition World.

Peano's original collection of axioms for the natural numbers contained two further
assumptions, which have not yet been mentioned in the tutorial:

```lean
succ_inj {a b : MyNat} :
  succ a = succ b → a = b

zero_ne_succ (a : MyNat) :
  zero ≠ succ a
 ```

The reason they have not been used yet is that they are both implications, that is, of the form `P ⟹ Q`.
This is clear for `succ_inj a b`, which says that for all `a` and `b` we have `succ a = succ b ⟹ a = b`.
For `zero_ne_succ` the trick is that `X ≠ Y` is *defined to mean* `X = Y ⟹ false`. If you have
understood through [Proposition world](../PropositionWorld.lean.md), you now have the required Lean
skills (i.e., you know the required tactics) to work with these implications.

Let's dive in: [Level 1](./AdvancedAdditionWorld/Level1.lean.md)

-/
