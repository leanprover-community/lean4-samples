import Lean
open Lean Elab Widget

@[widget]
def rubiks : UserWidgetDefinition := {
  name := "Rubik's cube"
  javascript:= include_str "widget" / "dist" / "rubiks.js"
}

structure RubiksProps where
  seq : Array String := #[]
  deriving ToJson, FromJson, Inhabited

def eg : RubiksProps := {seq := #["L", "L", "D⁻¹", "U⁻¹", "L", "D", "D", "L", "U⁻¹", "R", "D", "F", "F", "D"]}

#widget rubiks (toJson eg)
