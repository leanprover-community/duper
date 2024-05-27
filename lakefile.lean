import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"91cd0e81ec8bd16baa2c08e3d00a7f8e473477b4"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.8.0-rc2"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
