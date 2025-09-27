import Lake

open Lake DSL

require auto from git "https://github.com/JOSHCLUNE/lean-auto.git"@"querySMT"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.22.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
