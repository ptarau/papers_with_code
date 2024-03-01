%:-['/bin/prolog3d'].
:-[syn].

syn3d(E):-
  synthesize_circuit(E,Us:T:O,Size,Steps),
  !,
  pp_clause(Us:E:T),
  println([ttable=O,size=Size,steps=Steps]),
  draw_term(T).

draw_term(T):-prolog3d:show_term(T,30).

