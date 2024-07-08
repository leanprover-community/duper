import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"7e475ff3bd5aa241b783546ca9700016e7a617ff"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.8.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
