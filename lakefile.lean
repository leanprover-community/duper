import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"6cd81c96800dc2d2741499e931f350f069ca74c7"
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
