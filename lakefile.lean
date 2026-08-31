import Lake

open Lake DSL

-- The below commit is for the experimental "Monomorphization.saturate_refactor" branch of Lean-auto
require auto from git "https://github.com/leanprover-community/lean-auto.git"@"11528abcf2e530da983536049b8f762a68e6bd9c"
require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.33.0"

package Duper {
  precompileModules := true
  preferReleaseBuild := true 
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
