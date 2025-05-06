import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"8174c6f15a7bba75a1996caf69c83c2c15a46cce"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.18.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
