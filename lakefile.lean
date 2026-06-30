import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"main"
require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

package Duper {
  precompileModules := true
  preferReleaseBuild := true 
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
