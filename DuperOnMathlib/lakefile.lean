import Lake
open Lake DSL

package «duperOnMathlib» {
  -- add any package configuration options here
}

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "81dd376a02781030ead59ee35ca5334a7fccc527"

require «Duper» from "../"

@[default_target]
lean_lib «DuperOnMathlib» {
  -- add library configuration options here
}
