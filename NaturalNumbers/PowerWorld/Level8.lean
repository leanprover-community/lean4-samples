import MyNat.Power
import AdditionWorld.Level5 -- one_eq_succ_zero
import PowerWorld.Level3 -- pow_one
import AdditionWorld.Level6 -- simp additions
import MultiplicationWorld.Level7 -- add_mul
import MultiplicationWorld.Level9 -- simp additions
namespace MyNat
open MyNat

/-!
# Power World

## Level 8: `add_squared`

## Theorem
For all naturals `a` and `b`, we have `(a + b)^2 = a^2 + b^2 + 2ab`.

The first step in writing this proof is to convert `2` into something we
have theorems about, which is `1` and `0`.
-/
def two : MyNat := 2
def two_eq_succ_one : two = succ 1 := by rfl
lemma one_plus_one : (1 : MyNat) + (1 : MyNat) = (2 : MyNat) := by rfl
-- and we already have `one_eq_succ_zero`.

/-!
Now we are ready to tackle the proof:
-/

lemma add_squared (a b : MyNat) :
  (a + b) ^ two = a ^ two + b ^ two + 2 * a * b := by
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  repeat rw [pow_succ]
  repeat rw [pow_zero]
  repeat rw [one_mul]
  rw [mul_add]
  repeat rw [add_mul]
  rw [←one_plus_one]
  repeat rw [add_mul]
  repeat rw [one_mul]
  simp

/-!
It is also helpful to teach `simp` our new tricks:
-/
attribute [simp] pow_succ pow_one pow_zero

/-!
There is some fun discussion on [Lean Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/function.20with.20random.20definition/near/179723073)
about different ways to solve this one in fewer steps.
Feel free to try some of those solutions here, just note that the Lean 4 syntax is a bit different,
no commas between tactics, and square brackets are required on the `rw` tactic.

Do you fancy doing `(a+b)^3` now? You might want to read
[this Xena Project blog post](https://xenaproject.wordpress.com/2018/06/13/ab3/) before you start though.

If you got this far -- very well done! If you only learnt the three
tactics `rw`, `induction` and `rfl` then there are now more tactics to
learn; time to try [Function World](../FunctionWorld.lean.md).

The main thing we really want to impress upon people is that we believe
that *all of pure mathematics* can be done in this new way.

The [Liquid Tensor Experiment](https://xenaproject.wordpress.com/2022/09/12/beyond-the-liquid-tensor-experiment/)
shows that Lean can be used to prove very large math theorems.

Lean 3 also has a [definition of perfectoid spaces](https://leanprover-community.github.io/lean-perfectoid-spaces/)
(a very complex modern mathematical structure). We believe that these systems will one day
cause a paradigm shift in the way mathematics is done, but first we need
to build what we know, or at least build enough to state what we
mathematicians believe.

If you want to get involved, come and join
us at the [Zulip Lean chat](https://leanprover.zulipchat.com").
The `#new members` stream is a great place to start asking questions.

Next up [Function World](../FunctionWorld.lean.md).
-/