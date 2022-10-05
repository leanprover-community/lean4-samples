import MyNat.Definition -- Imports the natural numbers.
import MyNat.Addition -- imports addition.
open MyNat

lemma zero_add (n : MyNat) : zero + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [add_succ, ih]