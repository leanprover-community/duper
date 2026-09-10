import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"eb9c694863439fb55800228bc4c7babe42b089bf"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.33.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := true 
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
