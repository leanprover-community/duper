import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"7f6aec42310efd5c3311e944fff95cdabef4556a"
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
