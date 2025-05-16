import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"bceed7c8a99a0c8dc3cd644bbe75653bc70b77cd"
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
