import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"0728f384d78982e6fb0f1cdf263e172d3135e0be"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.12.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
