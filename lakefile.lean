import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"1d4ca366b60ca0927bacfa58172a58c3b81b8fee"
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
