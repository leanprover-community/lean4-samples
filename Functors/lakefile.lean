import Lake
open Lake DSL

package functors {
  -- add package configuration options here
}

lean_lib Functors {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe functors {
  root := `Main
}
