:-[csyn].
:-[funs].
:-[eval].

:-[tools].
:-[ttbits].

:-[tests].

/*
:-[nsyn].
:-[nif].
:-[rewrite].
% :-[dc].
*/

syn(E):-synthesize_circuit(E).

syn16:-synthesize_2_arg_boolean_operators.

%unpair(I,A,B):-cantor_unpair(I,A,B).
%pair(A,B,I):-cantor_pair(A,B,I).

unpair(Op,I,A,B):-call(Op,I,A,B).

unpair(I,A,B):-bitmix_unpair(I,A,B).
pair(A,B,I):-bitmix_pair(A,B,I).

pairop(Op,I,R):-unpair(I,A,B),call(Op,A,B,R).

psum(I,R):-pairop('+',I,R).
pprod(I,R):-pairop('*',I,R).

unpair_tree(Max,I,R):-unpair_tree(bitmix_unpair,Max,I,R).

unpair_tree(_Op,Max,X,R):-X<Max,R=X.
unpair_tree(Op,Max,N,t(X,Y)):-N>=Max,
  unpair(Op,N,A,B),
  unpair_tree(Op,Max,A,X),
  unpair_tree(Op,Max,B,Y).


axs:-
  A1=(P=>(Q=>P)),
  A2=((P=>(Q=>R))=>((P=>Q)=>(P=>R))),
  A3=((~R => ~Q)=>((~R=>Q)=>R)),
  IR=((P * (P=>Q)) => Q),
  All=[A1,A2,A3,IR],
  map(pp_clause,All),
  nl,
  foreach(member(X,All),syn(X)).
