import Lake
open Lake DSL

package listComprehension {
  -- add package configuration options here
}

lean_lib ListComprehension {
  -- add library configuration options here
}

@[default_target]
lean_exe listComprehension {
  root := `Main
}
