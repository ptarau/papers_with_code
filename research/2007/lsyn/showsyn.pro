:-[syn].

rshow(T):-val(show,tool,prolog3d),!,rli_call(localhost,prolog3d,gshow(T),_).
%rshow(T):-val(show,tool,prolog3d),!,prolog3d:show_term(T,30).
rshow(T):-rli_call(localhost,renoir,rshow(T),_).

ssyn(E,T):-
  synthesize_circuit(E,Us:T:O,Size,Steps),
  !,
  pp_clause(Us:E:T),
  println([ttable=O,size=Size,steps=Steps]).

ssyn(E):-ssyn(E,T),rshow(T).

dssyn(E):-ssyn(E,T),term_to_cat(T,C),dualize(C),rshow(C).
  
h(N):-int2ffs(N,T),println(T),rshow(T).
dh(N):-int2ffs(N,T),term_to_cat(T,C),dualize(C),rshow(C).

ur(N):-int2ur(N,1,T),println(T),rshow(T).
dur(N):-int2ur(N,1,T),term_to_cat(T,C),dualize(C),rshow(C).

u(N):-int2urcat(N,1,C),rshow(C).
du(N):-int2urcat(N,1,C),dualize(C),rshow(C).

v(B:N):-int2vurcat(B:N,C),rshow(C).
dv(B:N):-int2vurcat(B:N,C),dualize(C),rshow(C).

c(N):-cantor_tree(N,T),println(T),rshow(T).
dc(N):-cantor_tree(N,T),term_to_cat(T,C),dualize(C),rshow(C).

bt(N):-bitmix_tree(N,T),println(T),rshow(T).
dbt(N):-bitmix_tree(N,T),term_to_cat(T,C),dualize(C),rshow(C).

b(N):-int2bxcat(N,C),rshow(C).
db(N):-int2bxcat(N,C),dualize(C),rshow(C).

g(N):-int2graph(N,C),rshow(C).
dg(N):-int2graph(N,C),dualize(C),rshow(C).

p(N):-unpair_tree(3,N,T),rshow(T).

all:-
  B=4,
  random(X),N is abs(2+X mod 1000),
  println(showing(b=B,n=N)),
  v(B:N),sleep(2),
  dv(B:N),sleep(2),
  h(N),sleep(2),
  dh(N),sleep(2),
  ur(N),sleep(2),
  dur(N),sleep(2),
  c(N),sleep(2),
  c(N),sleep(2),
  bt(N),sleep(2),
  c(N),sleep(2),
  bt(N),sleep(2),
  b(N),sleep(2),
  db(N),sleep(2),
  g(N),sleep(2),
  dg(N),sleep(2),
  p(N),sleep(2).

% end
