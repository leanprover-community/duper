import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"v4.25.1-hammer"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.25.1"

package Duper {
  precompileModules := true
  preferReleaseBuild := true 
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
