import Duper.TPTP
import Duper.Tactic

-- set_option maxHeartbeats 80000

BEGIN_TPTP PUZ012_1'
tff(box_type,type,
    box: 🍉tType ).

tff(fruit_type,type,
    fruit: 🍉tType ).

tff(boxa_type,type,
    boxa: box ).

tff(boxb_type,type,
    boxb: box ).

tff(boxc_type,type,
    boxc: box ).

tff(apples_type,type,
    apples: fruit ).

tff(bananas_type,type,
    bananas: fruit ).

tff(oranges_type,type,
    oranges: fruit ).

tff(equal_fruits_type,type,
    equal_fruits: ( fruit * fruit ) > 🍉o ).

tff(equal_boxes_type,type,
    equal_boxes: ( box * box ) > 🍉o ).

tff(contains_type,type,
    contains: ( box * fruit ) > 🍉o ).

tff(label_type,type,
    label: ( box * fruit ) > 🍉o ).

tff(reflexivity_for_fruits,axiom,
    ! [X: fruit] : equal_fruits(X,X) ).

tff(reflexivity_for_boxes,axiom,
    ! [X: box] : equal_boxes(X,X) ).

tff(label_is_wrong,axiom,
    ! [X: box,Y: fruit] :
      ~ ( label(X,Y)
        & contains(X,Y) ) ).

tff(each_thing_is_in_a_box,axiom,
    ! [X: fruit] :
      ( contains(boxa,X)
      | contains(boxb,X)
      | contains(boxc,X) ) ).

tff(each_box_contains_something,axiom,
    ! [X: box] :
      ( contains(X,apples)
      | contains(X,bananas)
      | contains(X,oranges) ) ).

tff(contains_is_well_defined1,axiom,
    ! [X: box,Y: fruit,Z: fruit] :
      ( ( contains(X,Y)
        & contains(X,Z) )
     => equal_fruits(Y,Z) ) ).

tff(contains_is_well_defined2,axiom,
    ! [X: box,Y: fruit,Z: box] :
      ( ( contains(X,Y)
        & contains(Z,Y) )
     => equal_boxes(X,Z) ) ).

tff(boxa_not_boxb,axiom,
    ~ equal_boxes(boxa,boxb) ).

tff(boxb_not_boxc,axiom,
    ~ equal_boxes(boxb,boxc) ).

tff(boxa_not_boxc,axiom,
    ~ equal_boxes(boxa,boxc) ).

tff(apples_not_bananas,axiom,
    ~ equal_fruits(apples,bananas) ).

tff(bananas_not_oranges,axiom,
    ~ equal_fruits(bananas,oranges) ).

tff(apples_not_oranges,axiom,
    ~ equal_fruits(apples,oranges) ).

tff(boxa_labelled_apples,hypothesis,
    label(boxa,apples) ).

tff(boxb_labelled_oranges,hypothesis,
    label(boxb,oranges) ).

tff(boxc_labelled_bananas,hypothesis,
    label(boxc,bananas) ).

tff(boxb_contains_apples,hypothesis,
    contains(boxb,apples) ).

tff(prove_boxa_contains_bananas_and_boxc_oranges,conjecture,
    ( contains(boxa,bananas)
    & contains(boxc,oranges) ) ).
END_TPTP sorry

tptp KRS003_1 "../TPTP-v8.0.0/Problems/KRS/KRS003_1.p"
  by duper -- Succeeds

#print axioms KRS003_1

tptp COM001_1 "../TPTP-v8.0.0/Problems/COM/COM001_1.p"
  by duper -- Time: 73ms March 2

#print axioms COM001_1

tptp COM002_1 "../TPTP-v8.0.0/Problems/COM/COM002_1.p"
  by duper -- Time: 296ms March 2

#print axioms COM002_1

tptp COM002_2 "../TPTP-v8.0.0/Problems/COM/COM002_2.p"
  by duper -- Succeeds in finding a contradiction after changing isMaximalLit/isMaximalInSubClause to let maximal literals be incomparable

#print axioms COM002_2

tptp COM003_1 "../TPTP-v8.0.0/Problems/COM/COM003_1.p"
  by duper -- Fail to synthesize 'Inhabited algorithm'

/- Configurations that lead to COM003_1 achieving premature saturation include:
    - Having Order.lean consider variable names
    - Having a selection function that always returns the first negative literal

Note: It's noteworthy that in the final active set when COM003_1 achieves premature saturation, a large
number of clauses in the final active set include unknown free variables of the form '_uniq.XXXX'. Perhaps
these unknown free variables have something to do with the issue?

This is made even more plausible by the fact that, when COM003_1 DOESN'T achieve premature saturation, those free
variables are instead known variables of the form 'sk.XX'
-/

tptp HWV039_3 "../TPTP-v8.0.0/Problems/HWV/HWV039_3.p"
  by duper -- Number of lines 4435 in TPTP problem exceeded line number limit 4000

tptp PHI044_1 "../TPTP-v8.0.0/Problems/PHI/PHI044_1.p"
  by duper -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

tptp PUZ012_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ012_1.p"
  by duper -- Time: 130ms March 2

#print axioms PUZ012_1

tptp PUZ018_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ018_1.p"
  by duper -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

tptp PUZ031_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ031_1.p"
  by duper -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

tptp PUZ130_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ130_1.p"
  by duper -- Time: 11ms March 2

#print axioms PUZ130_1

tptp PUZ131_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ131_1.p"
  by duper -- Time: 22ms March 2

#print axioms PUZ131_1

tptp PUZ134_2 "../TPTP-v8.0.0/Problems/PUZ/PUZ134_2.p"
  by duper -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

tptp PUZ135_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ135_1.p"
  by duper -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

tptp PUZ135_2 "../TPTP-v8.0.0/Problems/PUZ/PUZ135_2.p"
  by duper -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

tptp PUZ139_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ139_1.p"
  by duper -- Succeeds

#print axioms PUZ139_1

tptp COM001_1_modified "../TPTP-v8.0.0/Problems/COM/COM001_1.p" by 
  have number_inhabited : Inhabited number := Inhabited.mk n
  duper -- Succeeds in finding a contradiction after commit that consumes the mData of expressions before converting them to literals

#print axioms COM001_1_modified
