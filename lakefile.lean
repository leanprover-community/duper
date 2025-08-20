import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"1e5d9f1477c7299ff6fbd7335c93c54cfd60b7a1"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.22.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
