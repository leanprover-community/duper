import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"3a973bb913c5b2db346a7e47b0b9bb6e3277e9b9"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
