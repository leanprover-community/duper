import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"1a4c55b6759a7084edea5aaa039254b0d52152b0"
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
