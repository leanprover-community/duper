import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"df285d9950123b2799ea71d9772d1a806f7d1e7a"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
