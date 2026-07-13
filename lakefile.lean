import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"fcbce0f216e71516e88b784944636da4d28ee780"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.32.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := true 
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
