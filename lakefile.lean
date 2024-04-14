import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"1282a544e84d33ade1fedfe494f16f96995b5d07"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
