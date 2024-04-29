import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"29d65a800b84cf2abe49c918acdfef7114b911ba"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
