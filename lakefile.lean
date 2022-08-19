import Lake

open Lake DSL

package Duper {
  precompileModules := true
}

lean_lib Duper

@[defaultTarget]
lean_exe defaultExe {
  root := `Main
}
