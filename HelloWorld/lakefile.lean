import Lake
open Lake DSL

package HelloWorld {
  -- add package configuration options here
}

lean_lib helloWorld {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe HelloWorld {
  root := `Main
}
