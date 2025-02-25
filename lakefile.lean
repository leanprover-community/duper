import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"76697fb30bbde1aac89bc51d33101b17764cd326"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.16.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
