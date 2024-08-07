import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"86a01b3e7979dada12daad7e1cc330d4a36ca156"
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
