import FunctionWorld.Level1
import FunctionWorld.Level2
import FunctionWorld.Level3
import FunctionWorld.Level4
import FunctionWorld.Level5
import FunctionWorld.Level6
import FunctionWorld.Level7
import FunctionWorld.Level8
import FunctionWorld.Level9
/-!

# Function world.

If you have finished playing with [Addition World](./AdditionWorld.lean), then you have got quite
good at manipulating equalities in Lean using the `rw` tactic. But there are plenty of levels later
on which will require you to manipulate functions, and `rw` is not the tool for you here.

To manipulate functions effectively, we need to learn about a new collection of tactics, namely
`exact`, `intro`, `have` and `apply`. These tactics are specially designed for dealing with
functions. Of course we are ultimately interested in using these tactics to prove theorems about the
natural numbers &ndash; but in this world there is little point in working with specific sets like
`MyNat`, everything works for general sets.

So our notation for this level is: `P`, `Q`, `R` and so on denote general sets,
and `h`, `j`, `k` and so on denote general
functions between them. What we will learn in this world is how to use functions
in Lean to push elements from set to set. A word of warning &ndash;
even though there's no harm at all in thinking of `P` being a set and `p`
being an element, you will not see Lean using the notation `p ∈ P`, because
internally Lean stores `P` as a "Type" and `p` as a "term", and it uses `p : P`
to mean "`p` is a term of type `P`", Lean's way of expressing the idea that `p`
is an element of the set `P`. You have seen this already &ndash; Lean has
been writing `n : MyNat` to mean that `n` is a natural number.

## A new kind of goal.

All through addition world, our goals have been theorems,
and it was our job to find the proofs.
**The levels in function world aren't theorems**. This is the only world where
the levels aren't theorems in fact. In function world the object of a level
is to create an element of the set in the goal. The goal will look like `⊢ X`
with `X` a set and you get rid of the goal by constructing an element of `X`.
I don't know if you noticed this, but you finished
essentially every goal of Addition World (and Multiplication World and Power World,
) with `rfl` or the implied `rfl` performed by `rw`.
This tactic is no use to us here.
We are going to have to learn a new way of solving goals &ndash; the `exact` tactic.

Let's begin with [Level 1](./FunctionWorld/Level1.lean.md).

-/