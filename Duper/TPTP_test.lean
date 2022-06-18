import Duper.TPTP
import Duper.Tactic

-- set_option maxHeartbeats 80000

BEGIN_TPTP PUZ012_1'
tff(box_type,type,
    box: $tType ).

tff(fruit_type,type,
    fruit: $tType ).

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
    equal_fruits: ( fruit * fruit ) > $o ).

tff(equal_boxes_type,type,
    equal_boxes: ( box * box ) > $o ).

tff(contains_type,type,
    contains: ( box * fruit ) > $o ).

tff(label_type,type,
    label: ( box * fruit ) > $o ).

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
  by duper -- Prover saturated!?

tptp COM001_1 "../TPTP-v8.0.0/Problems/COM/COM001_1.p"
  by duper -- Time: 309ms May 8

#print axioms COM001_1

tptp COM002_1 "../TPTP-v8.0.0/Problems/COM/COM002_1.p"
  by duper -- Time: 711ms May 8

#print axioms COM002_1

tptp COM002_2 "../TPTP-v8.0.0/Problems/COM/COM002_2.p"
  by duper -- Prover saturated

tptp COM003_1 "../TPTP-v8.0.0/Problems/COM/COM003_1.p"
  by duper -- Prover saturated

tptp HWV039_3 "../TPTP-v8.0.0/Problems/HWV/HWV039_3.p"
  by duper -- Time: 16663ms May 8

#print axioms HWV039_3

tptp PHI044_1 "../TPTP-v8.0.0/Problems/PHI/PHI044_1.p"
  by duper -- (deterministic) timeout at 'superposition', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

tptp PUZ012_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ012_1.p"
  by duper -- Time: 444ms May 8

#print axioms PUZ012_1

tptp PUZ018_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ018_1.p"
  by duper -- (deterministic) timeout at 'superposition', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

tptp PUZ031_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ031_1.p"
  by duper -- Prover saturated

tptp PUZ130_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ130_1.p"
  by duper -- Time: 61ms May 8

#print axioms PUZ130_1

tptp PUZ131_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ131_1.p"
  by duper -- Time: 76ms May 8

#print axioms PUZ131_1

tptp PUZ134_2 "../TPTP-v8.0.0/Problems/PUZ/PUZ134_2.p"
  by duper -- Contradiction found but failed to synthesize "Inhabited knowheyan"
           -- Note: After adding equality factoring, this test changed from the above result to a deterministic timeout

tptp PUZ135_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ135_1.p"
  by duper -- (deterministic) timeout at 'superposition', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)
/-
Note: After adding equality factoring, this test changed from the above result to:
  equalityFactoringWithAllConstraints: Types of second = reconstituted_materials_sculpture and reconstituted_materials_sculpture = first are not the same

I think this error makes sense, since reconstituted_materials_sculpture has the type entry and second has the type place, and there's no particular reason that elements
of those two types should be comparable. That said, it's not clear to me whether the fact there seem to already be equalities between different types indicates a bug or
oversight (either in the equality factoring code or elsewhere). So I think it would be worthwhile to spend some time looking into what's occuring in this example.

Second note: After adding ordering checks to equality resolution, PUZ135_1 returned to a deterministic timeout, but PUZ135_2 below began listing an extremely similar
error to the one described above. Also, if PUZ134_2 above is given the proof sorry, PUZ135_1 still returns the error described above (not 100% sure why though)
-/

tptp PUZ135_2 "../TPTP-v8.0.0/Problems/PUZ/PUZ135_2.p"
  by duper -- (deterministic) timeout at 'superposition', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)

tptp PUZ139_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ139_1.p"
  by duper -- <input>:1:281: expected tff_atomic_type

tptp COM001_1_modified "../TPTP-v8.0.0/Problems/COM/COM001_1.p" by 
  have number_inhabited : Inhabited number := Inhabited.mk n
  duper -- Succeeds in finding a contradiction after commit that consumes the mData of expressions before converting them to literals

#print axioms COM001_1_modified

tptp PUZ134_2_modified "../TPTP-v8.0.0/Problems/PUZ/PUZ134_2.p" by 
  have inhabited_knowheyan : Inhabited knowheyan := Inhabited.mk a
  duper 
/- PUZ134_2_modified gives the error: 
application type mismatch
h rfl
argument has type
  [anonymous] = [anonymous]
but function has type
  [anonymous] = [anonymous] → False

At present, I'm not sure how to interpret this error, or even whether it indicates a bug in duper or tptp
-/