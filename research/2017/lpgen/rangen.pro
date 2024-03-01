% adaptor for random generation
c:-['rangen.pro'].

:-include('fungen.pro').

member_choice(Choice,Choices):-
  length(Choices,L),L>0,
  I is random(L),
  nth0(I,Choices,Choice).

%select_choice(Choice,[X],[]):-!,Choice=X.
select_choice(Choice,Choices,ChoicesLeft):-
  length(Choices,L),L>0,
  I is random(L),
  nth0(I,Choices,Choice,ChoicesLeft).

between_choice(From,To,Choice):-
  Dist is To-From+1,
  Choice is From+random(Dist).

go:-pcg(8),pmg(8),pmc(8).

/* BUG
?- gen_term(21,[v/0,l/1,a/2,b/2],T),nv(T).
false.
*/