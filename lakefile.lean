import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"d014e03e1b8804473e5128175b8fa571a9dd4040"
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
