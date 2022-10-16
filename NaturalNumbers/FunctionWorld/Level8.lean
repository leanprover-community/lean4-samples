import MyNat.Definition
namespace MyNat
open MyNat

/-!
# Function World

## Level 8: `(P → Q) → ((Q → Empty) → (P → Empty))`

Level 8 is the same as level 7, except we have replaced the
set  `F` with the empty set `∅` (`Empty`). The same proof will work (after all, our
previous proof worked for all sets, and the empty set is a set).
But note that if you start with `intro f; intro h; intro p`
(which can incidentally be shortened to `intro f h p`,
see [intros tactic](../Tactics/intros.lean.md)),
then the local context looks like this:

```
P Q : Type
f : P → Q
h : Q → Empty
p : P
⊢ Empty
```

and your job is to construct an element of the empty set!
This on the face of it seems hard, but what is going on is that
our hypotheses (we have an element of `P`, and functions `P → Q`
and `Q → Empty`) are themselves contradictory, so
I guess we are doing some kind of proof by contradiction at this point? However,
if your next line is `apply h` then all of a sudden the goal
seems like it might be possible again. If this is confusing, note
that the proof of the previous world worked for all sets `F`, so in particular
it worked for the empty set, you just probably weren't really thinking about
this case explicitly beforehand. [Technical note to constructivists: I know
that we are not doing a proof by contradiction. But how else do you explain
to a classical mathematician that their goal is to prove something false
and this is OK because their hypotheses don't add up?]

## Definition

Whatever the sets `P` and `Q` are, we
make an element of \\(\operatorname{Hom}(\operatorname{Hom}(P,Q),
\operatorname{Hom}(\operatorname{Hom}(Q,\emptyset),\operatorname{Hom}(P,\emptyset)))\\).
-/
example (P Q : Type) : (P → Q) → ((Q → Empty) → (P → Empty)) := by
  intros f h p
  apply h
  apply f
  exact p

/-!

Next up [Level 9](./Level9.lean.md).
-/