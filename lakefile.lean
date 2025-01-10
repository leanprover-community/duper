import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"37a909c5dc093d7161ad499ebda30dc8a424468d"
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
