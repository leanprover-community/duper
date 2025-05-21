import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"32a1eeb7378646ec2314d4cf2820f3295f19b94b"
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
