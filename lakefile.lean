import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"v0.0.7"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
