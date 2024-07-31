import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"3101539f202f889339d1ad701859214875441617"
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
