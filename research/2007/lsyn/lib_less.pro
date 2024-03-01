:-[showsyn].

constant_functions(VarCount,[One],[1]):-all_ones_mask(VarCount,One).

combine_expression_values(_,L,R,O1,O2,(L<R),O):-bitless(O1,O2,O).

%end
