import MyNat.Addition
import MyNat.Multiplication
namespace MyNat
open MyNat

/-!
# Function world.

## Level 2: the `intro` tactic.

Let's make a function. Let's define the function on the natural
numbers which sends a natural number `n` to `3n+2`. In the example
below you will see that our goal is `⊢ MyNat → MyNat`. A mathematician
might denote this set with some exotic name such as `Hom(ℕ,ℕ)`,
but computer scientists use notation `X → Y` to denote the set of
functions from `X` to `Y` and this name definitely has its merits.
In type theory, `X → Y` is a type (the type of all functions from `X` to `Y`),
and `f : X → Y` means that `f` is a term
of this type, i.e., `f` is a function from `X` to `Y`.

To define a function `X → Y` we need to choose an arbitrary
element `x ∈ X` and then, perhaps using `x`, make an element of `Y`.
The Lean tactic for "let `x ∈ X` be arbitrary" is `intro x`.

## Rule of thumb:

If your goal is `P → Q` then `intro p` will make progress.

To solve the goal below, you have to come up with a function from `MyNat`
to `MyNat`. We can start with `intro n`

(i.e. "let `n ∈ ℕ` be arbitrary") and note that our
local context now looks like this:

```
n : MyNat
⊢ MyNat
```

Our job now is to construct a natural number, which is
allowed to depend on `n`. We can do this using `exact` and
writing a formula for the function we want to define. For example
we imported addition and multiplication at the top of this file,
so `exact 3*n+2`
will close the goal, ultimately defining the function `f(n)=3n+2`.


## Definition

We define a function from MyNat to MyNat.
-/
example : MyNat → MyNat := by
  intro n
  exact 3*n+2

/-!
You can hover your mouse over the tactics `intro` and `exact`
to the documentation on these tactics in case you need a
reminder later on.
See also [intro tactic](../Tactics/intro.lean.md)


Next up [Level 3](./Level3.lean.md).
-/