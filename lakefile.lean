import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"35dd124945e6fe3bcd05ce6c5631c471fc23e164"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.14.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
