import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"401933baa147f0c074d7fc65aaa1d282b480b331"
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
