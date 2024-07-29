import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"1ba441f1d385cc2a7eebd927a5d2aa71b40fbd7a"
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
