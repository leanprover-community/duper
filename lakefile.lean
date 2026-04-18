import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"32fe8491a6d85704932e813ee25c87e620123926"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.29.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := true 
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
