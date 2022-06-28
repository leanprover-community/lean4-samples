import Lake
open Lake DSL

package cSVParser {
  -- add package configuration options here
}

lean_lib CSVParser {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe csv {
  root := `Main
}
