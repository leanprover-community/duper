import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"915802517242f70b284fbcd5eac55bdaae29535e"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.13.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
