import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"8af43a276ecb2d7df4273af63bf74d69300988b6"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.16.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
