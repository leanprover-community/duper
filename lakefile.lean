import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"084da43b10a998dd9cd3115d1cbbaecb47734f9a"
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
