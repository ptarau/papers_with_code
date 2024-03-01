:-[showsyn].

constant_functions(VarCount,[0,One],[0,1]):-all_ones_mask(VarCount,One).

combine_expression_values(_,L,R,O1,O2,(L<R),O):-bitless(O1,O2,O).
combine_expression_values(_,L,R,O1,O2,(L>R),O):-bitgt(O1,O2,O).
combine_expression_values(_,L,R,O1,O2,L*R,O):-bitand(O1,O2,O).
combine_expression_values(_,L,R,O1,O2,L+R,O):-bitor(O1,O2,O).
combine_expression_values(_,L,R,O1,O2,L^R,O):-bitxor(O1,O2,O).
