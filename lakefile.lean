import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"18e8ef5cb290366a4d1a98aee41589f64be33d29"
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
