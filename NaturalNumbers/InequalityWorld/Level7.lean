import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import AdvancedAdditionWorld.Level11 -- add_right_eq_zero
namespace MyNat
open MyNat
/-!
# Inequality World

## Level 7: `le_zero`

We proved `add_right_eq_zero` back in advanced addition world.
Remember that you can do things like `have h2 := add_right_eq_zero h1`
if `h1 : a + c = 0`.

### Lemma : `le_zero`
For all naturals `a`, if `a ≤ 0` then `a = 0`.
-/
lemma le_zero (a : MyNat) (h : a ≤ 0) : a = 0 := by
  cases h with
  | _ c hc =>
    have hc := hc.symm
    exact add_right_eq_zero hc

/-!
Next up [Level 8](./Level8.lean.md).
-/
