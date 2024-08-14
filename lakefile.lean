import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"6a8c8ff9289f8c2d716bc14b90cb022ffe3ef2e9"
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
