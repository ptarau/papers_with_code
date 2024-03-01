:-[showsyn].

constant_functions(_VarCount,[],[]).

combine_expression_values(_,L,R,O1,O2,(L<R),O):-bitless(O1,O2,O).
combine_expression_values(NbOfBits,L,R,O1,O2,nor(L,R),O):-bitnor(NbOfBits,O1,O2,O).
