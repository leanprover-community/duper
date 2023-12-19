import Lake
open Lake DSL

package «duperOnMathlib» {
  -- add any package configuration options here
}

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.4.0-rc1"

require «Duper» from "../"

@[default_target]
lean_lib «DuperOnMathlib» {
  -- add library configuration options here
}
