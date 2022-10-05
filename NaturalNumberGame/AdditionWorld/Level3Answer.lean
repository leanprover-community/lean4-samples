import MyNat.Definition
import MyNat.Addition
open MyNat

lemma succ_add (a b : MyNat) : succ a + b = succ (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [add_succ]
    rw [ih]
    rw [add_succ]
