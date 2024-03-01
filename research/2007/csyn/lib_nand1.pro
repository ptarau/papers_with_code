:-[syn3d].

constant_functions(VarCount,[One],[1]):-all_ones_mask(VarCount,One).

combine_expression_values(NbOfBits,L,R,O1,O2,nand(L,R),O):-bitnand(NbOfBits,O1,O2,O).
