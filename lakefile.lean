import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"7d44184dc9581b07ff809b0341f3321315d48ce4"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.17.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
