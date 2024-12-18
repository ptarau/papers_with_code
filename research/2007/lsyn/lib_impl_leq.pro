:-[showsyn].

%constant_functions(_VarCount,[],[]).
%constant_functions(_VarCount,[0],[0]).
%constant_functions(VarCount,[One],[1]):-all_ones_mask(VarCount,One).
constant_functions(VarCount,[0,One],[0,1]):-all_ones_mask(VarCount,One).

combine_expression_values(NbOfBits,L,R,O1,O2,(L=>R),O):-bitimpl(NbOfBits,O1,O2,O).
combine_expression_values(_,L,R,O1,O2,(L<R),O):-bitless(O1,O2,O).

%end
