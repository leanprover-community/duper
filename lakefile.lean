import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"62faa00e45ffcf1871ca23bf4dcb10d918c0d679"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
