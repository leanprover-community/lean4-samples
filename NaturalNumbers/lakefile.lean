import Lake
open Lake DSL

package naturalNumberGame {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "56b19bdec560037016e326795d0feaa23b402c20"


lean_lib MyNat
lean_lib TutorialWorld
lean_lib AdditionWorld
lean_lib MultiplicationWorld
lean_lib PowerWorld
lean_lib FunctionWorld
lean_lib PropositionWorld
lean_lib AdvancedPropositionWorld