import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"680d6d58ce2bb65d15e5711d93111b2e5b22cb1a"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.12.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
