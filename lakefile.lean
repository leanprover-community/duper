import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"229863a28cc2f74782605254205cd86419d1627e"
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
