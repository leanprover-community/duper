import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"90d3e99954316c2add83341f528a2ab8d19d0a74"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.19.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
