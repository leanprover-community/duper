import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"87a8fcf2e82be6a9fd50b06bb4caaba20ef1c232"
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
