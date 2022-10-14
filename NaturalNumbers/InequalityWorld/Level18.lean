import MyNat.Definition
import MyNat.Power
import InequalityWorld.Level4 -- zero_le
import InequalityWorld.Level17 -- lt, lt_iff_succ_le
import MultiplicationWorld.Level4 -- mul_add
import MultiplicationWorld.Level8 -- mul_comm
namespace MyNat
open MyNat

lemma lt_irrefl (a : MyNat) : ¬ (a < a) := by
  intro h
  cases h with
  | _ h1 h2 =>
    apply h2
    exact h1

lemma ne_of_lt (a b : MyNat) : a < b → a ≠ b := by
  intro h
  intro h1
  cases h with
  | _ h2 h3 =>
    apply h3
    rw [h1]

theorem not_lt_zero (a : MyNat) : ¬(a < 0) := by
  intro h
  cases h with
  | _ ha hna =>
    apply hna
    exact zero_le a

theorem lt_of_lt_of_le (a b c : MyNat) : a < b → b ≤ c → a < c := by
  intro hab
  intro hbc
  rw [lt_iff_succ_le] at hab ⊢
  cases hbc with
  | _ x hx =>
    cases hab with
    | _ y hy =>
      rw [hx]
      rw [hy]
      use y + x
      rw [add_assoc]

theorem lt_of_le_of_lt (a b c : MyNat) : a ≤ b → b < c → a < c := by
  intro hab
  intro hbc
  rw [lt_iff_succ_le] at hbc ⊢
  cases hbc with
  | _ x hx =>
    cases hab with
    | _ y hy =>
      rw [hx]
      rw [hy]
      use y + x
      rw [succ_add]
      rw [succ_add]
      rw [add_assoc]

theorem lt_trans (a b c : MyNat) : a < b → b < c → a < c := by
  intro hab
  intro hbc
  rw [lt_iff_succ_le] at hab hbc ⊢
  cases hbc with
  | _ x hx =>
    cases hab with
    | _ y hy =>
      rw [hx]
      rw [hy]
      use y + x + 1
      repeat rw [succ_add]
      repeat rw [succ_eq_add_one]
      simp

theorem lt_iff_le_and_ne (a b : MyNat) : a < b ↔ a ≤ b ∧ a ≠ b := by
  constructor
  {
    intro h
    cases h with
    | _ h1 h2 =>
      constructor
      assumption
      intro h
      apply h2
      rw [h]
  }
  {
    intro h
    cases h with
    | _ h1 h2 =>
    constructor
    exact h1
    intro h
    apply h2
    exact le_antisymm _ _ h1 h
  }

theorem lt_succ_self (n : MyNat) : n < succ n := by
  rw [lt_iff_le_and_ne]
  constructor
  {
    use 1
  }
  {
    intro h
    exact ne_succ_self n h
  }

lemma succ_le_succ_iff (m n : MyNat) : succ m ≤ succ n ↔ m ≤ n := by
  constructor
  {
    intro h
    cases h with
    | _ c hc =>
      use c
      apply succ_inj
      rw [hc]
      rw [succ_add]
  }
  {
    intro h
    cases h with
    | _ c hc =>
      use c
      rw [hc]
      rw [succ_add]
  }


lemma lt_succ_iff_le (m n : MyNat) : m < succ n ↔ m ≤ n := by
  rw [lt_iff_succ_le]
  exact succ_le_succ_iff m n


lemma le_of_add_le_add_left (a b c : MyNat) : a + b ≤ a + c → b ≤ c := by
  intro h
  cases h with
  | _ d hd =>
    use d
    apply add_left_cancel a
    rw [hd]
    rw [add_assoc]

lemma lt_of_add_lt_add_left (a b c : MyNat) : a + b < a + c → b < c := by
  repeat rw [lt_iff_succ_le]
  intro h
  apply le_of_add_le_add_left a
  rw [add_succ]
  assumption

lemma add_lt_add_right (a b : MyNat) : a < b → ∀ c : MyNat, a + c < b + c := by
  intro h
  intro c
  rw [lt_iff_succ_le] at h ⊢
  cases h with
  | _ d hd =>
    use d
    rw [hd]
    repeat rw [succ_add]
    rw [add_right_comm]

-- BUGBUG: collectibles
-- and now we get three achievements!
-- instance : ordered_comm_monoid MyNat :=
-- { add_le_add_left := λ _ _, add_le_add_left,
--   lt_of_add_lt_add_left := lt_of_add_lt_add_left,
--   ..MyNat.add_comm_monoid, ..MyNat.partial_order}
-- instance : canonically_ordered_monoid MyNat :=
-- { le_iff_exists_add := le_iff_exists_add,
--   bot := 0,
--   bot_le := zero_le,
--   ..MyNat.ordered_comm_monoid,
--   }
-- instance : ordered_cancel_comm_monoid MyNat :=
-- { add_left_cancel := add_left_cancel,
--   add_right_cancel := add_right_cancel,
--   le_of_add_le_add_left := le_of_add_le_add_left,
--   ..MyNat.ordered_comm_monoid}

def succ_lt_succ_iff (a b : MyNat) : succ a < succ b ↔ a < b := by
  repeat rw [lt_iff_succ_le]
  exact succ_le_succ_iff _ _

-- multiplication

theorem mul_le_mul_of_nonneg_left (a b c : MyNat) : a ≤ b → 0 ≤ c → c * a ≤ c * b := by
  intro hab
  intro h0
  cases hab with
  | _ d hd =>
    rw [hd]
    rw [mul_add]
    use c * d

theorem mul_le_mul_of_nonneg_right (a b c : MyNat) : a ≤ b → 0 ≤ c → a * c ≤ b * c := by
  intro hab
  intro h0
  rw [mul_comm]
  rw [mul_comm b]
  apply mul_le_mul_of_nonneg_left
  assumption
  assumption

theorem mul_lt_mul_of_pos_left (a b c : MyNat) : a < b → 0 < c → c * a < c * b := by
  intro hab
  intro hc
  cases c with
  | zero =>
    exfalso
    exact lt_irrefl 0 hc
  | succ d =>
    clear hc
    induction d with
    | zero =>
      rw [succ_mul, zero_is_0, zero_mul, zero_add, succ_mul, zero_mul, zero_add]
      exact hab
    | succ e he =>
      rw [succ_mul]
      rw [succ_mul (succ e)]
      have h := succ e * a + a < succ e * b + a
      exact add_lt_add_right _ _ he _
      apply lt_trans _ _ _ h
      rw [add_comm]
      rw [add_comm _ b]
      apply add_lt_add_right
      assumption

theorem mul_lt_mul_of_pos_right (a b c : MyNat) : a < b → 0 < c → a * c < b * c := by
  intros ha h0
  rw [mul_comm]
  rw [mul_comm b]
  apply mul_lt_mul_of_pos_left
  assumption
  assumption

-- And now another achievement! The naturals are an ordered semiring.
-- instance : ordered_semiring MyNat :=
-- { mul_le_mul_of_nonneg_left := mul_le_mul_of_nonneg_left,
--   mul_le_mul_of_nonneg_right := mul_le_mul_of_nonneg_right,
--   mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left,
--   mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right,
--   ..MyNat.semiring,
--   ..MyNat.ordered_cancel_comm_monoid
-- }

lemma le_mul (a b c d : MyNat) : a ≤ b → c ≤ d → a * c ≤ b * d := by
  intros hab hcd
  induction a with
  | zero =>
    rw [zero_is_0, zero_mul]
    apply zero_le
  | succ t Ht =>
    have cz := 0 ≤ c
    apply zero_le
    have bz := 0 ≤ b
    apply zero_le
    apply mul_le_mul hab hcd cz bz

lemma pow_le (m n a : MyNat) : m ≤ n → m ^ a ≤ n ^ a := by
  intro h
  induction a with
  | zero =>
    rw [zero_is_0, pow_zero, pow_zero]
  | succ t Ht =>
    rw [pow_succ, pow_succ]
    apply le_mul
    assumption
    assumption

lemma strong_induction_aux (P : MyNat → Prop)
  (IH : ∀ m : MyNat, (∀ b : MyNat, b < m → P b) → P m)
  (n : MyNat) : ∀ c < n, P c := by
  induction n with
  | zero =>
    intro c
    intro hc
    exfalso
    revert hc
    exact not_lt_zero c
  | succ d hd =>
    intros e he
    rw [lt_succ_iff_le] at he
    apply IH
    intros b hb
    apply hd
    exact lt_of_lt_of_le _ _ _ hb he

theorem strong_induction (P : MyNat → Prop)
  (IH : ∀ m : MyNat, (∀ d : MyNat, d < m → P d) → P m) :
  ∀ n, P n := by
  intro n
  apply strong_induction_aux P IH (succ n)
  exact lt_succ_self n

