import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"d90cb1aadbd52bf885958efa292ff4ef4f649732"
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
