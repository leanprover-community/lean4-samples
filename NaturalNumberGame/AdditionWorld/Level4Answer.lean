import MyNat.Definition
import MyNat.Addition
import AdditionWorld.Level1Answer -- add_zero
import AdditionWorld.Level3Answer -- succ_add
open MyNat

lemma add_comm (a b : MyNat) : a + b = b + a := by
  induction b with
  | zero =>
    rw [add_zero]
    rw [zero_add]
  | succ b ih =>
    rw [add_succ]
    rw [ih]
    rw [succ_add]
