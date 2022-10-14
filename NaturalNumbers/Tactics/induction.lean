import MyNat.Definition
/-!
# Tactic : induction

Assuming `x` is a variable in the local context with an inductive type, `induction x` applies induction
on `x` to the main goal, producing one goal for each constructor of the inductive type, in which the
target is replaced by a general instance of that constructor and an inductive hypothesis is added
for each recursive argument to the constructor. If the type of an element in the local context
depends on `x`, that element is reverted and reintroduced afterward, so that the inductive hypothesis
incorporates that hypothesis as well.

For example, given `n : Nat` and a goal with a hypothesis `h : P n` and target `Q n`, `induction n` produces
one goal with hypothesis `h : P 0` and target `Q 0`, and one goal with hypotheses `h : P (Nat.succ a)` and
`ih₁ : P a → Q a` and target `Q (Nat.succ a)`. Here the names `a` and `ih₁` are chosen automatically and are
not accessible. You can use `with` to provide the variables names for each constructor.

`induction e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then
performs induction on the resulting variable. `induction e using r` allows the user to specify the
principle of induction that should be used. Here `r` should be a theorem whose result type must be of
the form `C t`, where `C` is a bound variable and `t` is a (possibly empty) sequence of bound variables
`induction e generalizing z₁ ... zₙ`, where `z₁ ... zₙ` are variables in the local context, generalizes
over `z₁ ... zₙ` before applying the induction but then introduces them in each goal. In other words,
the net effect is that each inductive hypothesis is generalized. Given `x : Nat`,

`
induction x with
| zero => tac₁
| succ x' ih => tac₂
`
uses tactic `tac₁` for the `zero` case, and `tac₂` for the `succ` case.
-/
