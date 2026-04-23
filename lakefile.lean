import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"786fdbc7ed7a5340f044fd7dd6ef67b87b605d58"
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
