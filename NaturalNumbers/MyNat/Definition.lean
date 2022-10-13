import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
namespace MyNat

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat
deriving BEq, DecidableEq, Inhabited

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

theorem zero_is_0 : MyNat.zero = 0 := by rfl

def one : MyNat := MyNat.succ 0