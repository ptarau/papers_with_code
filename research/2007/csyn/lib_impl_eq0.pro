:-[syn3d].

constant_functions(_VarCount,[0],[0]).

combine_expression_values(NbOfBits,L,R,O1,O2,(L=>R),O):-bitimpl(NbOfBits,O1,O2,O).

combine_expression_values(NbOfBits,L,R,O1,O2,L=R,O):-biteq(NbOfBits,O1,O2,O).

%end
