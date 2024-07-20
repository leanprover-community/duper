import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"542821345b1e8eb8e244dacafa96d677d0a55340"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.9.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
