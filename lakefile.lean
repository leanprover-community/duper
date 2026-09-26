import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"040019783b6bec7a47abf6d51fa39ee89b0a402f"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.34.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := true 
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
