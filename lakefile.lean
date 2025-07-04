import Lake

open Lake DSL

require auto from git "https://github.com/hanwenzhu/lean-auto.git" @ "hammer-bump-v4.21.0"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.21.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
