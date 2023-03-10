import Duper.TPTP
import Duper.Tactic

set_option trace.Rule.boolSimp true in
tptp ITP209_2 "../TPTP-v8.0.0/Problems/ITP/ITP209_2.p"
  by duper