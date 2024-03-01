:-[showsyn].

%constant_functions(_VarCount,[],[]). % needs 1 - cannot synthetise it
constant_functions(VarCount,[One],[1]):-all_ones_mask(VarCount,One).

combine_expression_values(NbOfBits,L,R,O1,O2,(L=>R),O):-bitimpl(NbOfBits,O1,O2,O).
combine_expression_values(_,L,R,O1,O2,L^R,O):-bitxor(O1,O2,O).
