import MyNat.Definition
namespace MyNat
open MyNat

axiom mul_zero (a : MyNat) : a * 0 = 0

axiom mul_succ (a b : MyNat) : a * (succ b) = a * b + a