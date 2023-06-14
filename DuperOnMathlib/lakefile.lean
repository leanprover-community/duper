import Lake
open Lake DSL

package «duperOnMathlib»

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "bac7310"
require «duper» from "../"

@[default_target]
lean_lib «DuperOnMathlib» {
  -- add library configuration options here
}
