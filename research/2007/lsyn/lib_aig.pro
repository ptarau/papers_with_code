:-[showsyn].

constant_functions(_VarCount,[],[]).

combine_expression_values(_NbOfBits,L,R,O1,O2,L*R,O):-bitand(O1,O2,O).
combine_expression_values(NbOfBits,L,R,O1,O2,nand(L,R),O):-bitnand(NbOfBits,O1,O2,O).
