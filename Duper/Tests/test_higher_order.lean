import Duper.Tactic
import Duper.TPTP

set_option trace.Meta.debug true in
set_option trace.Prover.saturate true in
tptp NUM020_1 "../TPTP-v8.0.0/Problems/NUM/NUM020^1.p"
  by duper -- Time: 444ms May 8