import Lake

open Lake DSL

require std from git "https://github.com/leanprover/std4.git"@"main"

require auto from git "https://github.com/avigad/lean-auto.git"

package Duper {
  precompileModules := true
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
