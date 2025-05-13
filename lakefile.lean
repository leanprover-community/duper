import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"f68ef29887f9d09a40a8b4bc06c9482ab5b643da"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.20.0-rc2"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
