import Lake

open Lake DSL

require std from git "https://github.com/leanprover/std4.git"@"eb43042ebfebcc111ccd1986d3f7615cdf986a0d"

package Duper {
  precompileModules := true
}

lean_lib Duper

@[default_target]
lean_exe defaultExe {
  root := `Main
}
