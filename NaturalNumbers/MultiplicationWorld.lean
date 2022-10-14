import MultiplicationWorld.Level1
import MultiplicationWorld.Level2
import MultiplicationWorld.Level3
import MultiplicationWorld.Level4
import MultiplicationWorld.Level5
import MultiplicationWorld.Level6
import MultiplicationWorld.Level7
import MultiplicationWorld.Level8
import MultiplicationWorld.Level9
/-!
# Multiplication World

A new import `import MyNat.Multiplication`!

This import gives you the definition of multiplication on your natural numbers. It is defined by
recursion, just like addition. Here are the two new axioms:

  * `mul_zero (a : MyNat) : a * 0 = 0`
  * `mul_succ (a b : MyNat) : a * succ b = a * b + a`

In words, we define multiplication by "induction on the second variable", with `a * 0` defined to be
`0` and, if we know `a * b`, then `a` times the number after `b` is defined to be `a * b + a`.

You can keep all the theorems you proved about addition, but for multiplication, those two results
above are what you've got right now.

What's going on in multiplication world? Like addition, we need to go for the proofs that
multiplication is commutative and associative, but as well as that we will need to prove facts about
the relationship between multiplication and addition, for example `a * (b + c) = a * b + a * c`, so
now there is a lot more to do. Good luck!

You have been given `mul_zero`, and the first thing to prove is `zero_mul`.
Like `zero_add`, we of course prove it by induction.

Let's get started with  [Multiplication Level 1](./MultiplicationWorld/Level1.lean.md).
-/