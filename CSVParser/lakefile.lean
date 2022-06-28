import Lake
open Lake DSL

package CSVParser {
  -- add package configuration options here
}

lean_lib cSVParser {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe CSVParser {
  root := `Main
}
