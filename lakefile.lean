import Lake

open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git"@"997d810f10945740fb68923fbfa0cdf84636d07c"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.15.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := false
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
