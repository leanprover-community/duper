import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"ad14dd82f885bbbde39d799bcad852501e3f7c9a"
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
