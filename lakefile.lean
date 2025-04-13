import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"cab3e33cf347574104753eabc4269097fc25d82d"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.18.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
