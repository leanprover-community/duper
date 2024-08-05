import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"6b4f64a11d1b76853086b86118d854d8277f6609"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.9.1"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
