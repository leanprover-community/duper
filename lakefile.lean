import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"7e55decbdfcb338407d9b09c28441d42d34047de"
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
