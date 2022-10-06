import Lake
open Lake DSL

package naturalNumberGame {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "56b19bdec560037016e326795d0feaa23b402c20"


lean_lib MyNat {
  -- add library configuration options here
}

lean_lib TutorialWorld {
  -- add library configuration options here
}


lean_lib AdditionWorld {
  -- add library configuration options here
}

lean_lib MultiplicationWorld {
  -- add library configuration options here
}
