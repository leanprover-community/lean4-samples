import InequalityWorld.Level1
import InequalityWorld.Level2
import InequalityWorld.Level3
import InequalityWorld.Level4
import InequalityWorld.Level5
import InequalityWorld.Level6
import InequalityWorld.Level7
import InequalityWorld.Level8
import InequalityWorld.Level9
import InequalityWorld.Level10
import InequalityWorld.Level11
import InequalityWorld.Level12
import InequalityWorld.Level13
import InequalityWorld.Level14
import InequalityWorld.Level15
import InequalityWorld.Level16
import InequalityWorld.Level17
-- import InequalityWorld.Level18 -- BUGBUG

/-!
# Inequality World

A new `import MyNat.Inequality` gives us a new definition. If `a` and `b` are naturals,
`a ≤ b` is *defined* to mean

`∃ (c : MyNat), b = a + c`

The backwards E means "there exists". So in words, `a ≤ b`
if and only if there exists a natural number `c` such that `b=a+c`.

If you really want to change an `a ≤ b` to `∃ c, b = a + c` then
you can do so with `rw [le_iff_exists_add]`:

```lean
axiom le_iff_exists_add (a b : MyNat) :
  a ≤ b ↔ ∃ (c : MyNat), b = a + c
```

But because `a ≤ b` is *defined as* `∃ (c : MyNat), b = a + c`, you
do not need to `rw [le_iff_exists_add]`, you can just pretend when you see `a ≤ b`
that it says `∃ (c : MyNat), b = a + c`. You will see a concrete
example of this in level 1.

A new construction like `∃` means that we need to learn how to manipulate it.
There are two situations. Firstly we need to know how to solve a goal
of the form `⊢ ∃ c, ...`, and secondly we need to know how to use a hypothesis
of the form `∃ c, ...`.

Let's dive in [Level 1](./InequalityWorld/Level1.lean.md).

-/