import Lean
import Duper.TPTPParser.Basic

open Lean
open Lean.Parser

@[run_parser_attribute_hooks] def sqstr : Parser :=
  withAntiquot (mkAntiquot "singleQuotedLit" singleQuotedStrKind) singleQuotedStrNoAntiquot

-- test

/- Successful
syntax "[sing|" sqstr "]" : term

macro_rules
|`([sing| $sql]) =>
  let h := Lean.Syntax.mkStrLit (Lean.Syntax.getSingleQuotedStr sql)
  `($h)

#eval [sing|'asdkd']
-/