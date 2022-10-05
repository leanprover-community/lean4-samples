import MyNat.Definition
import MyNat.Addition
import AdditionWorld.Level2Answer -- add_assoc
import AdditionWorld.Level4Answer -- add_comm
open MyNat


lemma add_right_comm (a b c : MyNat) : a + b + c = a + c + b := by
  rw [add_assoc]
  rw [add_comm b c]
  rw [←add_assoc]