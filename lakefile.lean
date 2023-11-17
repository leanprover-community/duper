import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"40791afa955f0472a2ee510e790adf0d34fe65b2"

package Duper {
  precompileModules := true
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
