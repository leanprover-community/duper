import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"e2baae0f47b8cd331acc44ec46e67da0b376848c"
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
