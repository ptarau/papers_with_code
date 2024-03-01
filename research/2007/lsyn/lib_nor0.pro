:-[showsyn].

constant_functions(_VarCount,[0],[0]).

combine_expression_values(NbOfBits,L,R,O1,O2,nor(L,R),O):-bitnor(NbOfBits,O1,O2,O).
