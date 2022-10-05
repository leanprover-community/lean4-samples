import MyNat.Definition
open MyNat

/--
This theorem proves that if you add zero to a MyNat you get back the same number.
-/
theorem add_zero (a : MyNat) : a + zero = a := by rfl

/--
This theorem proves that (a + (d + 1)) = ((a + d) + 1) for a,d in MyNat.
-/
theorem add_succ (a d : MyNat) : a + (succ d) = succ (a + d) := by rfl
