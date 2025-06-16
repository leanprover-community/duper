import Lake

open Lake DSL

<<<<<<< hammer-v4.21.0-rc3
require auto from git "https://github.com/hanwenzhu/lean-auto.git" @ "hammer-bump-v4.21.0-rc3"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.21.0-rc3"
=======
require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "hammer"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.20.0"
>>>>>>> hammer

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
