import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"0f5f39a0336e36ae4ba8ab45b27865ebd9f8f025"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.8.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
