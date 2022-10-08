import Duper.TPTP
import Duper.Tactic

tptp PUZ018_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ018_1.p"
  by duper -- Success

tptp PUZ031_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ031_1.p"
  by duper -- Failed to synthesize inhabited_plant

tptp PUZ031_1_modified "../TPTP-v8.0.0/Problems/PUZ/PUZ031_1.p" by 
  have inhabited_plant : Inhabited plant := sorry
  duper -- Error when reconstructing clausification

tptp PUZ137_8 "../TPTP-v8.0.0/Problems/PUZ/PUZ137_8.p"
  by duper -- Prover saturated (noted in TODO.md)

/-
tptp PUZ081_8 "../TPTP-v8.0.0/Problems/PUZ/PUZ081_8.p" -- Parsing issue
  by duper PUZ081_8
-/

tptp PUZ083_8 "../TPTP-v8.0.0/Problems/PUZ/PUZ083_8.p"
  by duper -- Succeeds

tptp PUZ134_2 "../TPTP-v8.0.0/Problems/PUZ/PUZ134_2.p"
  by duper -- Failed to synthesize inhabited ?α

tptp PUZ135_2 "../TPTP-v8.0.0/Problems/PUZ/PUZ135_2.p"
  by duper -- Det timeout

tptp PUZ082_8 "../TPTP-v8.0.0/Problems/PUZ/PUZ082_8.p"
  by duper -- Succeeds

tptp PUZ130_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ130_1.p"
  by duper -- Succeeds

tptp PUZ131_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ131_1.p"
  by duper -- Succeeds

tptp PUZ135_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ135_1.p"
  by duper -- Det timeout

tptp PUZ134_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ134_1.p"
  by duper -- Det timeout

tptp PUZ139_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ139_1.p"
  by duper -- Succeeds

/-
tptp PUZ133_2 "../TPTP-v8.0.0/Problems/PUZ/PUZ133=2.p" -- Parsing issue
  by duper PUZ133_2
-/

tptp PUZ012_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ012_1.p"
  by duper -- See TODO

#print axioms PUZ018_1
#print axioms PUZ031_1
#print axioms PUZ137_8
--#print axioms PUZ081_8
#print axioms PUZ083_8
#print axioms PUZ134_2
#print axioms PUZ135_2
#print axioms PUZ082_8
#print axioms PUZ130_1
#print axioms PUZ131_1
#print axioms PUZ135_1
#print axioms PUZ134_1
#print axioms PUZ139_1
--#print axioms PUZ133_2
#print axioms PUZ012_1