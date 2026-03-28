import Lake

open Lake DSL

require auto from git "https://github.com/JOSHCLUNE/lean-auto.git"@"querySMT"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.29.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := true 
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
