import Lake
open Lake DSL

package guessMyNumber {
  -- add package configuration options here
}

lean_lib GuessMyNumber {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe guess {
  root := `Main
}
