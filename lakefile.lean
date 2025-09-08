import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"531948548693fc867b2187635742083984f08818"
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
