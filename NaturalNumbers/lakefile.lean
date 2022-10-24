import Lake
open Lake DSL

package naturalNumberGame {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "9efcb9508435caeb4281b14455f37b88f8ffc2e5"


lean_lib MyNat
lean_lib TutorialWorld
lean_lib AdditionWorld
lean_lib MultiplicationWorld
lean_lib PowerWorld
lean_lib FunctionWorld
lean_lib PropositionWorld
lean_lib AdvancedPropositionWorld
lean_lib AdvancedAdditionWorld
lean_lib AdvancedMultiplicationWorld
lean_lib InequalityWorld