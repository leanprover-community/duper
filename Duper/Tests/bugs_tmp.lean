import Duper.TPTP
import Duper.Tactic

set_option trace.Prover.saturate true in
tptp SEU139 "../TPTP-v8.0.0/Problems/SEU/SEU139+1.p"
  by duper