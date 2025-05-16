import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"b9a5fa7a88410474c13905bd23d331ea079923b3"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.20.0-rc2"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
