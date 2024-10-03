import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"2b6ed7d9f86d558d94b8d9036a637395163c4fa6"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.11.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
