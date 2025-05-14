import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"1cbb77c4d8ce485ba752fac414e0ea81ec87b699"
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
