:-[showsyn].

constant_functions(_VarCount,[],[]).
%constant_functions(VarCount,[0,One],[0,1]):-all_ones_mask(VarCount,One).

combine_expression_values(NbOfBits,L,R,O1,O2,nand(L,R),O):-bitnand(NbOfBits,O1,O2,O).
combine_expression_values(NbOfBits,L,R,O1,O2,nor(L,R),O):-bitnor(NbOfBits,O1,O2,O).
