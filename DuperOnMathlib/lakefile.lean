import Lake
open Lake DSL

package «duperOnMathlib» {
  -- add any package configuration options here
}

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "4e5518cafc0efd7c7b7d287fa960fce5201908db"

require «Duper» from "../"

@[default_target]
lean_lib «DuperOnMathlib» {
  -- add library configuration options here
}
