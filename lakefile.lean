import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"2a2b34778c9b7023d8f6e2484eb56eadfa05ecc8"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.32.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := true 
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
