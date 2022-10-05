import MyNat.Definition
import MyNat.Addition
open MyNat

lemma add_assoc (a b c : MyNat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero =>
    -- ⊢ a + b + 0 = a + (b + 0)
    rw [add_zero]
    rw [add_zero]
  | succ c ih =>
    -- ⊢ (a + b) + succ d = a + (b + succ d)
    rw [add_succ]
    rw [add_succ]
    rw [add_succ]
    rw [ih]

