import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"51a9dfdda6810bba95693cad2d72195ed0caf986"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
