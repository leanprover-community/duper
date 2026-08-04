import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"1175ff6b958ad9513fe4830f9fca11ebe59eb78d"
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
