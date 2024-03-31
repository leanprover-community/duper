import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"8ff83d69a1c29288be936ae938d2402b498ee14b"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
