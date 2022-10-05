import MyNat.Definition
import MyNat.Addition
import AdditionWorld.Level1Answer -- add_zero
import AdditionWorld.Level3Answer -- succ_add
open MyNat

axiom one_eq_succ_zero : (1 : MyNat) = MyNat.succ 0

theorem succ_eq_add_one (n : MyNat) : succ n = n + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rfl