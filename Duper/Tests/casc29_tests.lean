import Duper.Tactic
import Duper.TPTP

-- THF
-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/GEG/GEG013\^1.p --timeout=10 gets ResourceOut (with and without ho; with and without avatar)
tptp GEG013__1 "../TPTP-v8.0.0/Problems/GEG/GEG013^1.p"
  by duper

-- 4.39s in competition. Parsing issue here
-- zipperposition ../TPTP-v8.0.0/Problems/CSR/CSR144\^1.p --ho=true --timeout=10 --avatar=off achieves Theorem in 0.017s
tptp CSR144__1 "../TPTP-v8.0.0/Problems/CSR/CSR144^1.p"
  by duper

-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/SEU/SEU796^1.p --timeout=10 gets ResourceOut (with and without ho; with and without avatar)
tptp SEU796__1 "../TPTP-v8.0.0/Problems/SEU/SEU796^1.p"
  by duper

-- 3.72s in competition. Constructed proof in 148ms here
tptp PUZ081__3 "../TPTP-v8.0.0/Problems/PUZ/PUZ081^3.p"
  by duper

-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/SET/SET609^3.p --timeout=10 gets ResourceOut (with and without ho; with and without avatar)
tptp SET609__3 "../TPTP-v8.0.0/Problems/SET/SET609^3.p"
  by duper

-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/SYO/SYO180\^5.p --ho=true --timeout=10 achieves Theorem in 0.006s
  -- The proof uses 'esa cnf' and 'esa split' a lot and then closes by inf 'sat_resolution*'. So it seems this test
  -- is significantly aided by the use of Avatar
-- zipperposition ../TPTP-v8.0.0/Problems/SYO/SYO180\^5.p --ho=true --timeout=10 --avatar=off also achieves Theorem in 0.010s
  -- The proof uses cnf, demod, inf s_sup-, and clc. Duper should be able to support each of these, so this is a good candidate
  -- for more closely examining where duper is going wrong.
tptp SYO180__5 "../TPTP-v8.0.0/Problems/SYO/SYO180^5.p"
  by duper

-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/SET/SET611^3.p --timeout=10 gets ResourceOut (with and without ho; with and without avatar)
tptp SET611__3 "../TPTP-v8.0.0/Problems/SET/SET611^3.p"
  by duper

-- 3.53s in competition. Constructed proof in 34 ms here
tptp NUM791__1 "../TPTP-v8.0.0/Problems/NUM/NUM791^1.p"
  by duper

-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/SEU/SEU572^1.p --timeout=10 gets ResourceOut (with and without ho; with and without avatar)
tptp SEU572__1 "../TPTP-v8.0.0/Problems/SEU/SEU572^1.p"
  by duper

-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/SYO/SYO560^1.p --timeout=10 gets GaveUp in 0.030s (with and without ho; with and without avatar)
tptp SYO560__1 "../TPTP-v8.0.0/Problems/SYO/SYO560^1.p"
  by duper

-- FOF
-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/SEU/SEU321+1.p --ho=true --timeout=10 --avatar=off achieves Theorem in 0.053s
  -- The proof uses cnf, inf s_sup-, and demod. Duper should be able to support each of these, so this is a good candidate
  -- for more closely examining where duper is going wrong.
tptp SEU321__1 "../TPTP-v8.0.0/Problems/SEU/SEU321+1.p"
  by duper

-- TMO in competition. Too many lines to parse here
-- For what it's worth, zipperposition also gets ResourceOut
tptp CSR048__3 "../TPTP-v8.0.0/Problems/CSR/CSR048+3.p"
  by duper

-- 20.77s in competition. Det timeout here (though presumably it'd be solved if I extended the heartbeats)
-- zipperposition ../TPTP-v8.0.0/Problems/SYO/SYO560^1.p --ho=true --timeout=10 --avatar=off achieves Theorem in 6.476s
  -- The proof uses cnf, inf s_sup-, and demod. This isn't a good candidate to examine more closely due to length
tptp GEO620__1 "../TPTP-v8.0.0/Problems/GEO/GEO620+1.p"
  by duper

-- TMO in competition. Constructed proof in 728ms here
tptp NUN062__1 "../TPTP-v8.0.0/Problems/NUN/NUN062+1.p"
  by duper

-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/SWV/SWV158+1.p --ho=true --timeout=10 --avatar=off achieves Theorem in 0.509s
-- From a brief skim, this looks like it might be a good candidate to examine more closely, except that the terms are quite long
tptp SWV158__1 "../TPTP-v8.0.0/Problems/SWV/SWV158+1.p"
  by duper

-- TMO in competition. Parsing issue here (probably due to the length of the included axioms file)
-- Zipperposition can solve this locally, though it's not a helpful test to examine since the issue here is simply parsing
tptp CSR034__2 "../TPTP-v8.0.0/Problems/CSR/CSR034+2.p"
  by sorry

-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/GEO/GEO111+1.p --timeout=10 gets ResourceOut (with and without ho; with and without avatar)
tptp GEO111__1 "../TPTP-v8.0.0/Problems/GEO/GEO111+1.p"
  by duper

-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/CSR/CSR067+3.p --ho=true --timeout=10 --avatar=off achieves Theorem in 4.252s
-- The generated proof is relatively short but the time Zipperposition took and clause numbers indicates that Zipperposition
-- had to churn through a lot of clauses before finding this proof
tptp CSR067__3 "../TPTP-v8.0.0/Problems/CSR/CSR067+3.p"
  by duper

-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/SET/SET776+4.p --timeout=10 gets ResourceOut (with and without ho; with and without avatar)
tptp SET776__4 "../TPTP-v8.0.0/Problems/SET/SET776+4.p"
  by duper

-- TMO in competition. Det timeout here
-- zipperposition ../TPTP-v8.0.0/Problems/KRS/KRS194+1.p --timeout=10 gets ResourceOut (with and without ho; with and without avatar)
tptp KRS194__1 "../TPTP-v8.0.0/Problems/KRS/KRS194+1.p"
  by duper

-- Tests that might merit a closer look:
-- SYO180^5, SEU321+1, SWV158+1