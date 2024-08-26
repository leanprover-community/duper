import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"22d4c2e7f2453e16b9d980cae2367d38bedf3bf5"
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
