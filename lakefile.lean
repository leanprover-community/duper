import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"0a4b392a33e942b8a145f5e3f26f8f08dd311b1c"

package Duper {
  precompileModules := true
  preferReleaseBuild := true
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
