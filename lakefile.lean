import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"320d2cdf10d8d9875b0533a61023ee589b8e08e5"
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
