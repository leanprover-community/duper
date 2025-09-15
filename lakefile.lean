import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"2c986b111ac17d448d81b988fc8c794375d603d7"
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
