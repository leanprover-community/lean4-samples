import Lake
open Lake DSL

package helloWorld {
  -- add package configuration options here
}

lean_lib HelloWorld {
  -- add library configuration options here
}

@[default_target]
lean_exe hello {
  root := `Main
}
