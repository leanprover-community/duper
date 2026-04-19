import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"bdbf41bf8a8c25ebdeca6c7d5a11d5cc55c2f266"
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
