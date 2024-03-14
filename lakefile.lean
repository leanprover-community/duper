import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"1507142f79f05371e5eb25202eec6396bb940d72"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
