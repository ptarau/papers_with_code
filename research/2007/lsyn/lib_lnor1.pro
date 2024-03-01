:-[showsyn].

constant_functions(VarCount,[One],[1]):-all_ones_mask(VarCount,One).

combine_expression_values(_,L,R,O1,O2,(L<R),O):-bitless(O1,O2,O).
combine_expression_values(NbOfBits,L,R,O1,O2,nor(L,R),O):-bitnor(NbOfBits,O1,O2,O).
