import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"4d73b99262f1ce80a33ac832bef26549cf3c2034"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.14.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
