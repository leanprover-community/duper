import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"227b84888419d73814edbdc0d95f05ea738548bf"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.23.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
