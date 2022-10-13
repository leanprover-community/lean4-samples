import PropositionWorld.Level1
import PropositionWorld.Level2
import PropositionWorld.Level3
import PropositionWorld.Level4
import PropositionWorld.Level5
import PropositionWorld.Level6
import PropositionWorld.Level7
import PropositionWorld.Level8
import PropositionWorld.Level9
/-!

# Proposition world.

A Proposition is a true/false statement, like `2 + 2 = 4` or `2 + 2 = 5`.
Just like we can have concrete sets in Lean like `MyNat`, and abstract
sets called things like `X`, we can also have concrete propositions like
`2 + 2 = 5` and abstract propositions called things like `P`.

Mathematicians are very good at conflating a theorem with its proof.
They might say "now use theorem 12 and we're done". What they really
mean is "now use the proof of theorem 12..." (i.e. the fact that we proved
it already). Particularly problematic is the fact that mathematicians
use the word Proposition to mean "a relatively straightforward statement
which is true" and computer scientists use it to mean "a statement of
arbitrary complexity, which might be true or false". Computer scientists
are far more careful about distinguishing between a proposition and a proof.
For example: `x + 0 = x` is a proposition, and `add_zero x`
is its proof. The convention we'll use is capital letters for propositions
and small letters for proofs.

In this world you will see the local context in the following kind of state:

```
P : Prop
p : P
```

Here `P` is the true/false statement (the statement of proposition), and `p` is its proof.
It's like `P` being the set and `p` being the element. In fact, computer scientists
sometimes think about the following analogy: propositions are like sets,
and their proofs are like their elements.

## What's going on in this world?

We're going to learn about manipulating propositions and proofs.
Fortunately, we don't need to learn a bunch of new tactics -- the
ones we just learnt (`exact`, `intro`, `have`, `apply`) will be perfect.

The levels in proposition world are "back to normal", we're proving
theorems, not constructing elements of sets. Or are we?

In Lean, Propositions, like sets, are types, and proofs, like elements of sets, are terms.


Let's get started [Level 1](./PropositionWorld/Level1.lean.md)
-/