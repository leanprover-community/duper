import Lake
open Lake DSL

package «duperOnMathlib»

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "57e4e03dd1782a74cf937835bbdb5f90955e4406"
require «duper» from "../"

@[default_target]
lean_lib «DuperOnMathlib» {
  -- add library configuration options here
}
