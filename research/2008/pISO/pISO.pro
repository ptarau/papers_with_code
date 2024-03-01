compose(iso(F,G),iso(F1,G1),iso(fcompose(F1,F),fcompose(G,G1))).
itself(iso(id,id)).
invert(iso(F,G),iso(G,F)).

fcompose(G,F,X,Y):-call(F,X,Z),call(G,Z,Y).
id(X,X).
from(iso(F,_),X,Y):-call(F,X,Y).
to(iso(_,G),X,Y):-call(G,X,Y).

borrow(IsoName,H,X,Y):-
  call(IsoName,iso(F,G)),
  fcompose(F,fcompose(H,G),X,Y).

lend(IsoName,H,X,Y):-
  call(IsoName,Iso),
  invert(Iso,iso(F,G)),
  fcompose(F,fcompose(H,G),X,Y).

fit(Op,IsoN,X,Y):-
  call(IsoN,Iso),
  fit_iso(Op,Iso,X,Y).

fit_iso(Op,Iso,X,Y):-
  from(Iso,X,Z),
  call(Op,Z,Y).
  
retrofit(Op,IsoN,X,Y):-
  call(IsoN,Iso),
  retrofit_iso(Op,Iso,X,Y).

retrofit_iso(Op,Iso,X,Y):-
  to(Iso,X,Z),
  call(Op,Z,Y).  

with(Iso1,Iso2,Iso):-
  invert(Iso2,Inv2),
  compose(Iso1,Inv2,Iso).
   
as(That,This,X,Y):-
  call(That,ThatF),
  call(This,ThisF),
  with(ThatF,ThisF,Iso),
  to(Iso,X,Y).

fun(Iso) :-itself(Iso).

set(iso(set2fun,fun2set)).

set2fun([],[]).
set2fun([X|Xs],[X|Fs]):-
  sort([X|Xs],[_|Ys]),
  set2fun(Ys,X,Fs).

set2fun([],_,[]).
set2fun([X|Xs],Y,[A|As]):-A is (X-Y)-1,set2fun(Xs,X,As).

fun2set([],[]).
fun2set([A|As],Xs):-findall(X,prefix_sum(A,As,X),Xs).

prefix_sum(A,As,R):-append(Ps,_,As),length(Ps,L),
  sumlist(Ps,S),R is A+S+L.

nat_set(iso(nat2set,set2nat)). 

nat2set(N,Xs):-nat2elements(N,Xs,0).

nat2elements(0,[],_K).
nat2elements(N,NewEs,K1):-N>0,
  B is /\(N,1),N1 is N>>1,K2 is K1+1,add_el(B,K1,Es,NewEs),
  nat2elements(N1,Es,K2).

add_el(0,_,Es,Es).
add_el(1,K,Es,[K|Es]).

set2nat(Xs,N):-set2nat(Xs,0,N).

set2nat([],R,R).
set2nat([X|Xs],R1,Rn):-R2 is R1+(1<<X),set2nat(Xs,R2,Rn).

nat(Iso):-
  nat_set(NatSet),
  set(Set),
  compose(NatSet,Set,Iso).

unrank(F,N,R):-call(F,N,Y),unranks(F,Y,R).
unranks(F,Ns,Rs):-maplist(unrank(F),Ns,Rs).

rank(G,Ts,Rs):-ranks(G,Ts,Xs),call(G,Xs,Rs).
ranks(G,Ts,Rs):-maplist(rank(G),Ts,Rs).

tsize1(Xs,N):-sumlist(Xs,S),N is S+1.

tsize(T,N) :- rank(tsize1,T,N).

hylo(IsoN,iso(rank(G),unrank(F))):-call(IsoN,iso(F,G)).

hylos(IsoN,iso(ranks(G),unranks(F))):-call(IsoN,iso(F,G)).

hfs(Iso) :- 
  hylo(nat_set,Hylo),
  nat(Nat),
  compose(Hylo,Nat,Iso).

hfs_succ(H,R):-borrow(nat_hfs,succ,H,R).
nat_hfs(Iso):-
  nat(Nat),
  hfs(HFS),
  with(Nat,HFS,Iso).

ackermann(N,H):-as(nat,hfs,N,H).
inverse_ackermann(H,N):-as(hfs,nat,H,N).

hff(Iso) :- 
  hylo(nat,Hylo),
  nat(Nat),
  compose(Hylo,Nat,Iso).  

bitpair(p(I,J),P):- 
  evens(I,Es),
  odds(J,Os),
  append(Es,Os,Ps),
  set2nat(Ps,P).
  
evens(X,Es):-nat2set(X,Ns),maplist(double,Ns,Es).
odds(X,Os):-evens(X,Es),maplist(succ,Es,Os).
double(N,D):-D is 2*N.

bitunpair(N,p(E,O)):-
  nat2set(N,Ns),
  split_evens_odds(Ns,Es,Os),
  set2nat(Es,E),
  set2nat(Os,O).
  
split_evens_odds([],[],[]).
split_evens_odds([X|Xs],[E|Es],Os):-
  X mod 2 =:= 0,
  E is X // 2,
  split_evens_odds(Xs,Es,Os).
split_evens_odds([X|Xs],Es,[O|Os]):-
  X mod 2 =:= 1,
  O is X // 2,
  split_evens_odds(Xs,Es,Os).

nat2(Iso):-
  nat(Nat),
  compose(iso(bitpair,bitunpair),Nat,Iso).

digraph2set(Ps,Ns) :- maplist(bitpair,Ps,Ns).
set2digraph(Ns,Ps) :- maplist(bitunpair,Ns,Ps).

digraph(Iso):-
  set(Set),
  compose(iso(digraph2set,set2digraph),Set,Iso).

set2hypergraph(S,G) :- maplist(nat2set,S,G).
hypergraph2set(G,S) :- maplist(set2nat,G,S).

hypergraph(Iso):-
  set(Set),
  compose(iso(hypergraph2set,set2hypergraph),Set,Iso).

nth(Thing,N,X) :- as(Thing,nat,N,X).

stream_of(Thing,X) :- nat_stream(N),nth(Thing,N,X).

nat_stream(0).
nat_stream(N):-nat_stream(N1),succ(N1,N).

random_gen(Thing,Max,Len,X):-
  random_fun(Max,Len,Ns),
  as(Thing,fun,Ns,X).
  
random_fun(Max,Len,Ns):-
  length(Ns,Len),
  maplist(random_nat(Max),Ns).

random_nat(Max,N):-random(X),N is integer(Max*X).
     

length_as(Thing,X,Len) :-
  nat(Nat),
  call(Thing,T),
  with(Nat,T,Iso), 
  fit_iso(length,Iso,X,Len).

sum_as(Thing,X,Len) :-
  nat(Nat),
  call(Thing,T),
  with(Nat,T,Iso), 
  fit_iso(sumlist,Iso,X,Len).

size_as(Thing,X,Len) :-
  nat(Nat),
  call(Thing,T),
  with(Nat,T,Iso), 
  fit_iso(tsize,Iso,X,Len).

strange_sort(Unsorted,Sorted):-
  nat_set(Iso),
  to(Iso,Unsorted,Ns),
  from(Iso,Ns,Sorted).

