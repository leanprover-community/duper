import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"main"

package Duper {
  precompileModules := true
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
