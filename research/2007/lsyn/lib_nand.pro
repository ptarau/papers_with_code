:-[showsyn].

constant_functions(_VarCount,[],[]).

combine_expression_values(NbOfBits,L,R,O1,O2,nand(L,R),O):-bitnand(NbOfBits,O1,O2,O).

% end
