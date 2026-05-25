import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"e247c6347f483037049d769129aef1593b258425"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.29.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := true 
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
