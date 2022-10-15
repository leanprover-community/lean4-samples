import MyNat.Addition -- imports addition.
namespace MyNat
open MyNat
/-!
# Addition World

## Level 2: `add_assoc` -- associativity of addition.

It's well-known that (1 + 2) + 3 = 1 + (2 + 3) -- if you have three numbers
to add up, it doesn't matter which of the additions you do first. This fact
is called *associativity of addition* by mathematicians, and it is *not*
obvious. For example, subtraction really is not associative: `(6 - 2) - 1`
is really not equal to `6 - (2 - 1)`. We are going to have to prove
that addition, as defined the way we've defined it, is associative.

To prove associativity of addition it is handy to recall that addition was defined
by recursion on the right-most variable. This means you can use induction on the right-most
variable (try other variables at your peril!). Note that when Lean writes `a + b + c`,
it means `(a + b) + c`. If it wants to talk about `a + (b + c)` it will put the brackets
in explicitly.

Reminder: you are done when you see "Goals accomplished 🎉" in the InfoView, and no
errors in the VS Code Problems list.

**Lemma**

On the set of natural numbers, addition is associative.
In other words, for all natural numbers `a, b` and `c`, we have
` (a + b) + c = a + (b + c). `
-/

lemma add_assoc (a b c : MyNat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero =>
    -- ⊢ a + b + 0 = a + (b + 0)
    rw [zero_is_0]
    rw [add_zero]
    rw [add_zero]
  | succ c ih =>
    -- ⊢ (a + b) + succ d = a + (b + succ d)
    rw [add_succ]
    rw [add_succ]
    rw [add_succ]
    rw [ih]

/-!
On to [Level 3](./Level3.lean.md).
-/


