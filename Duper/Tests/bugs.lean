import Duper.TPTP
import Duper.Tactic

-- Deterministic timeout
-- More saturate loops than commit `c1afee181ad15b58edba6972d3acef4e85eba7ed`
--   "support for recursors"
set_option maxHeartbeats 200000
set_option trace.Meta.debug true in
tptp GEO192 "../TPTP-v8.0.0/Problems/GEO/GEO192+2.p" by duper

-- βη reduction bug
set_option trace.Meta.debug true in
set_option trace.Prover.saturate true in
tptp NUM020_1 "../TPTP-v8.0.0/Problems/NUM/NUM020^1.p"
  by duper

tptp COM025_5 "../TPTP-v8.0.0/Problems/COM/COM025_5.p"
  by duper

tptp HWV042 "../TPTP-v8.0.0/Problems/HWV/HWV042_1.p"
  by duper

set_option maxTPTPProblemLines 10000 in
tptp ITP222 "../TPTP-v8.0.0/Problems/ITP/ITP222_2.p"
  by sorry

set_option maxTPTPProblemLines 10000 in
tptp ITP010_7 "../TPTP-v8.0.0/Problems/ITP/ITP010_7.p"
  by sorry

