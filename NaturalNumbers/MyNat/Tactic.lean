import Lean.PrettyPrinter.Delaborator.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Tactic.Replace
import Lean.Elab.Command

-- https://github.com/forked-from-1kasper/ground_zero/blob/master/GroundZero/Meta/Tactic.lean
open Lean

section
  variable {A : Sort u} (ρ : A → A → Sort v)

  class Reflexive :=
  (intro (a : A) : ρ a a)

  class Symmetric :=
  (intro (a b : A) : ρ a b → ρ b a)

  class Transitive :=
  (intro (a b c : A) : ρ a b → ρ b c → ρ a c)
end

section
  variable {A : Sort u} {B : Sort v} {C : Sort w}

  variable (ρ : A → B → Sort u')
  variable (η : B → C → Sort v')
  variable (μ : outParam (A → C → Sort w'))

  class Rewrite :=
  (intro (a : A) (b : B) (c : C) : ρ a b → η b c → μ a c)
end

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Lean/Expr/Basic.lean#L100-L109
def Lean.Expr.constName (e : Expr) : Name :=
e.constName?.getD Name.anonymous

def Lean.Expr.getAppFnArgs (e : Expr) : Name × Array Expr :=
withApp e λ e a => (e.constName, a)

namespace GroundZero.Meta.Tactic

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Ring.lean#L411-L419
def applyOnBinRel (name : Name) (rel : Name) : Elab.Tactic.TacticM Unit := do
  let mvars ← Elab.Tactic.liftMetaMAtMain (λ mvar => do
    let ε ← instantiateMVars (← MVarId.getDecl mvar).type
    ε.consumeMData.withApp λ e es => do
      unless (es.size > 1) do Meta.throwTacticEx name mvar s!"expected binary relation, got “{e} {es}”"

      let e₃ := es.back; let es := es.pop;
      let e₂ := es.back; let es := es.pop;

      let ty  ← Meta.inferType e₂
      let ty' ← Meta.inferType e₃

      unless (← Meta.isDefEq ty ty') do Meta.throwTacticEx name mvar s!"{ty} ≠ {ty'}"

      let u ← Meta.getLevel ty
      let v ← Meta.getLevel ε

      let ι ← Meta.synthInstance (mkApp2 (Lean.mkConst rel [u, v]) ty (mkAppN e es))
      let φ := (← Meta.reduceProj? (mkProj rel 0 ι)).getD ι

      MVarId.apply mvar φ)
  Elab.Tactic.replaceMainGoal mvars

section
  elab "reflexivity"  : tactic => applyOnBinRel `reflexivity  `Reflexive
  elab "symmetry"     : tactic => applyOnBinRel `symmetry     `Symmetric
  elab "transitivity" : tactic => applyOnBinRel `transitivity `Transitive
end
