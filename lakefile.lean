import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"bfb20f93b4e67029b977f218c67d8ca87ca09c9a"
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
