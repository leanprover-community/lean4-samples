import Lake
open Lake DSL

package quine {
  -- add package configuration options here
}

lean_lib Quine {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe quine {
  root := `Main
}
