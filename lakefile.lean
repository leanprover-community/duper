import Lake

open Lake DSL

package Duper

lean_lib Duper

@[defaultTarget]
lean_exe defaultExe {
  root := `Main
}
