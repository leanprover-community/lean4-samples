import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

instance : Inhabited MyNat where
  default := MyNat.zero

def myNatFromNat (x : Nat) : MyNat :=
  match x with
  | Nat.zero   => MyNat.zero
  | Nat.succ b => MyNat.succ (myNatFromNat b)

def natFromMyNat (x : MyNat) : Nat :=
  match x with
  | MyNat.zero   => Nat.zero
  | MyNat.succ b => Nat.succ (natFromMyNat b)

instance : OfNat MyNat n where
  ofNat := myNatFromNat n

instance : ToString MyNat where
  toString p := toString (natFromMyNat p)

def MyNat.add : MyNat → MyNat → MyNat
  | a, 0   => a
  | a, MyNat.succ b => MyNat.succ (MyNat.add a b)

instance : Add MyNat where
  add := MyNat.add

def MyNat.mul : MyNat → MyNat → MyNat
  | _, 0   => 0
  | a, b + 1 => a + (MyNat.mul a b)

instance : Mul MyNat where
  mul := MyNat.mul


-- def MyNat.pred : MyNat → MyNat
--   | 0      => 0
--   | succ a => a

-- def MyNat.sub : MyNat → MyNat → MyNat
--   | a, 0      => a
--   | a, succ b => pred (MyNat.sub a b)

-- instance : Sub MyNat where
--   sub := MyNat.sub

-- inductive MyNat.le (n : MyNat) : MyNat → Prop
--   /-- Less-equal is reflexive: `n ≤ n` -/
--   | refl     : MyNat.le n n
--   /-- If `n ≤ m`, then `n ≤ m + 1`. -/
--   | step {m} : MyNat.le n m → MyNat.le n (succ m)

-- protected def MyNat.lt (n m : MyNat) : Prop :=
--   MyNat.le (succ n) m

-- instance : LE MyNat where
--   le := MyNat.le

-- instance : LT MyNat where
--   lt := MyNat.lt

-- def MyNat.ble : MyNat → MyNat → Bool
--   | zero,   zero   => true
--   | zero,   succ _ => true
--   | succ _, zero   => false
--   | succ n, succ m => ble n m

-- theorem MyNat.zero_le : (n : MyNat) → LE.le 0 n
--   | zero   => MyNat.le.refl
--   | succ n => MyNat.le.step (zero_le n)

-- theorem MyNat.succ_le_succ : LE.le n m → LE.le (succ n) (succ m)
--   | MyNat.le.refl   => MyNat.le.refl
--   | MyNat.le.step h => MyNat.le.step (succ_le_succ h)

-- theorem MyNat.le_of_ble_eq_true (h : Eq (MyNat.ble n m) true) : LE.le n m :=
--   match n, m with
--   | 0,      _      => MyNat.zero_le _
--   | succ _, succ _ => MyNat.succ_le_succ (le_of_ble_eq_true h)

-- theorem MyNat.ble_self_eq_true : (n : MyNat) → Eq (MyNat.ble n n) true
--   | 0      => rfl
--   | succ n => ble_self_eq_true n

-- theorem MyNat.ble_succ_eq_true : {n m : MyNat} → Eq (MyNat.ble n m) true → Eq (MyNat.ble n (succ m)) true
--   | 0,      _,      _ => rfl
--   | succ n, succ _, h => ble_succ_eq_true (n := n) h

-- theorem MyNat.ble_eq_true_of_le (h : LE.le n m) : Eq (MyNat.ble n m) true :=
--   match h with
--   | MyNat.le.refl   => MyNat.ble_self_eq_true n
--   | MyNat.le.step h => MyNat.ble_succ_eq_true (ble_eq_true_of_le h)

-- theorem MyNat.not_le_of_not_ble_eq_true (h : Not (Eq (MyNat.ble n m) true)) : Not (LE.le n m) :=
--   fun h' => absurd (MyNat.ble_eq_true_of_le h') h

-- instance MyNat.decLe (n m : MyNat) : Decidable (LE.le n m) :=
--   dite (Eq (MyNat.ble n m) true) (fun h => isTrue (MyNat.le_of_ble_eq_true h)) (fun h => isFalse (MyNat.not_le_of_not_ble_eq_true h))

-- instance MyNat.decLt (n m :MyNat) : Decidable (LT.lt n m) :=
--   decLe (succ n) m

-- theorem MyNat.not_succ_le_zero : ∀ (n : MyNat), LE.le (succ n) 0 → False
--   | 0,      h => nomatch h
--   | succ _, h => nomatch h

-- protected theorem MyNat.le_trans {n m k : Nat} : LE.le n m → LE.le m k → LE.le n k
--   | h,  Nat.le.refl    => h
--   | h₁, Nat.le.step h₂ => Nat.le.step (Nat.le_trans h₁ h₂)

-- theorem MyNat.pred_le_pred : {n m : MyNat} → LE.le n m → LE.le (pred n) (pred m)
--   | _,           _, MyNat.le.refl   => MyNat.le.refl
--   | 0,      succ _, MyNat.le.step h => h
--   | succ _, succ _, MyNat.le.step h => MyNat.le_trans (le_succ _) h

-- theorem MyNat.le_of_succ_le_succ {n m : MyNat} : LE.le (succ n) (succ m) → LE.le n m :=
--   pred_le_pred

-- theorem MyNat.not_succ_le_self : (n : MyNat) → Not (LE.le (succ n) n)
--   | 0      => not_succ_le_zero _
--   | succ n => fun h => absurd (le_of_succ_le_succ h) (not_succ_le_self n)

-- protected theorem MyNat.lt_irrefl (n : MyNat) : Not (LT.lt n n) :=
--   MyNat.not_succ_le_self n

-- theorem sub_lt : ∀ {n m : MyNat}, 0 < n → 0 < m → n - m < n
--   | 0,   _,   h1, _  => absurd h1 (MyNat.lt_irrefl 0)
--   | _+1, 0,   _, h2  => absurd h2 (MyNat.lt_irrefl 0)
--   | n+1, m+1, _,  _  =>
--     Eq.symm (succ_sub_succ_eq_sub n m) ▸
--       show n - m < succ n from
--       lt_succ_of_le (sub_le n m)

-- theorem div_rec_lemma {x y : MyNat} : 0 < y ∧ y ≤ x → x - y < x :=
--   fun ⟨ypos, ylex⟩ => sub_lt (MyNat.lt_of_lt_of_le ypos ylex) ypos


-- def MyNat.div (x y : MyNat) : MyNat :=
--   if 0 < y ∧ y ≤ x then
--     MyNat.div (x - y) y + 1
--   else
--     0
-- decreasing_by apply div_rec_lemma; assumption

-- instance : Div Nat := ⟨Nat.div⟩

-- #eval Nat.div (7 : MyNat) (3 : MyNat)