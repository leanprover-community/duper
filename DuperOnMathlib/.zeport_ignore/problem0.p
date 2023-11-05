thf(sortdecl_nat, type, s_nat: $tType).
thf(sortdecl_int, type, s_int: $tType).
thf(sortdecl_string, type, s_string: $tType).
thf(sortdecl_empty, type, s_empty: $tType).
thf(sortdecl_1, type, s_a1: $tType).
thf(sortdecl_0, type, s_a0: $tType).

thf(typedecl_t_a5, type, t_a5: (s_a1 > (s_a0 > $o))).
thf(typedecl_t_a4, type, t_a4: (s_a0 > (s_a0 > s_a0))).
thf(typedecl_t_a3, type, t_a3: s_a0).
thf(typedecl_t_a2, type, t_a2: s_a0).
thf(typedecl_t_a1, type, t_a1: (s_a0 > (s_a0 > s_a0))).
thf(typedecl_t_a0, type, t_a0: (s_a0 > (s_a0 > s_a0))).

thf(fact0, axiom, ((~) @ (((=) @ ((t_a0 @ ((t_a1 @ t_a2) @ t_a3)) @ ((t_a1 @ t_a3) @ t_a2))) @ ((t_a1 @ ((t_a0 @ t_a2) @ t_a3)) @ ((t_a4 @ t_a2) @ t_a3))))).
thf(fact1, axiom, (! [X0 : s_a0] : (! [X1 : s_a0] : (((=>) @ (! [X2 : s_a1] : (((=) @ ((t_a5 @ X2) @ X0)) @ ((t_a5 @ X2) @ X1)))) @ (((=) @ X0) @ X1))))).
thf(fact2, axiom, (! [X0 : s_a1] : (! [X1 : s_a0] : (! [X2 : s_a0] : (((=) @ ((t_a5 @ X0) @ ((t_a0 @ X1) @ X2))) @ (((|) @ ((t_a5 @ X0) @ X1)) @ ((t_a5 @ X0) @ X2))))))).
thf(fact3, axiom, (! [X0 : s_a1] : (! [X1 : s_a0] : (! [X2 : s_a0] : (((=) @ ((t_a5 @ X0) @ ((t_a4 @ X1) @ X2))) @ (((&) @ ((t_a5 @ X0) @ X1)) @ ((t_a5 @ X0) @ X2))))))).
thf(fact4, axiom, (! [X0 : s_a0] : (! [X1 : s_a0] : (! [X2 : s_a1] : (((=) @ ((t_a5 @ X2) @ ((t_a1 @ X0) @ X1))) @ (((&) @ ((t_a5 @ X2) @ X0)) @ ((~) @ ((t_a5 @ X2) @ X1)))))))).