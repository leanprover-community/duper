import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"5149acf1aaa07a62a53a7e0979ff79d85812287d"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.11.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
