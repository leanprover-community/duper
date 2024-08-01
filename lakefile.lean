import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"4bcc5ddd41533ebcad5fbc65ba46a76001101f0c"
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
