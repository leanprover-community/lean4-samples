import Lake
open Lake DSL

package GuessMyNumber {
  -- add package configuration options here
}

lean_lib guessMyNumber {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe GuessMyNumber {
  root := `Main
}
