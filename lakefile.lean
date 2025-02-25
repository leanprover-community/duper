import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"a9047f3d3206781c4940edcb328e689d6034446c"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.16.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
