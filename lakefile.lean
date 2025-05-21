import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"9a558f49f4997d19d69e50a90c2bbc98faff2476"
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
