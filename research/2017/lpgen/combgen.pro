% adaptor for combinatorial generation
c:-['combgen.pro'].

:-include('fungen.pro').

member_choice(Choice,Choices):-member(Choice,Choices).
select_choice(Choice,Choices,ChoicesLeft):-select(Choice,Choices,ChoicesLeft).
between_choice(From,To,I):-between(From,To,I).

go:-pcg(4),pmg(4),pmc(6).