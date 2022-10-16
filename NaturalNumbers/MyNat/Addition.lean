import MyNat.Definition
namespace MyNat
open MyNat

/--
This theorem proves that if you add zero to a `MyNat` you get back the same number.
-/

theorem add_zero (a : MyNat) : a + 0 = a := by rfl

/--
This theorem proves that `(a + (d + 1)) = ((a + d) + 1)` for `a` and `d` in `MyNat`.
-/
theorem add_succ (a d : MyNat) : a + (succ d) = succ (a + d) := by rfl
