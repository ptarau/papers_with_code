:-include('stats.pro').
:-include('catalan.pro').
:-include('motzkin.pro').
:-include('lambda.pro').
:-include('sk.pro').
:-include('catgram.pro').

% simple generator - using DCGs

spend(Fuel,From,To):-From>=Fuel,To is From-Fuel.

gen(N,Fs,T):-gen(Fs,T,N,0).

gen(Fs,T)-->{member(F/K,Fs)},gen_cont(K,F,Fs,T).

gen_cont(0,F,_,F)-->[].
gen_cont(K,F,Fs,T)-->{K>0},spend(K),{functor(T,F,K)},gens(Fs,0,K,T).

gens(_,N,N,_)-->[].
gens(Fs,I,N,T)-->{I1 is I+1,arg(I1,T,A)},gen(Fs,A),gens(Fs,I1,N,T).

% Remy-style generator by grafting on edges

classify_funs(FNs,Cs,SortedFs):-
 findall(N-F,member(F/N,FNs),NFs),
 sort(NFs,Ordered),
 group_pairs_by_key(Ordered,ByArityFs),
 keysort(ByArityFs,[0-Cs|SortedFs]).

get_arities(NFs,Ns):-maplist(arg(1),NFs,Ns).

init_funs(NFs,Ns,Root,Es):-
  get_arities(NFs,Ns),
  member_choice(N,Ns),
  init_fun(Root,N,Es).
  
init_fun(Root,N,Es):-N>0,
  length(Ns,N),N1 is N-1,numlist(0,N1,Is),
  maplist(=(N),Ns),
  maplist(make_edge(Root),Ns,Is,Es).
  
make_edge(X,N,I,e(N,I,X,_)).



% insert new term A by splitting edge X Y: X->A + A->Y
% insert leaves in all positions, except K to where it inserts a new edge from A

extension_step(GoodNs,OldEs,[e(M,I,X, A),e(Arity,K,A,Y)|Es],N1,N2):-
  GoodNs=[_|_],
  select_choice(e(M,I,X, Y),OldEs,OtherEs), % select an edge - bind M,I 
  % select a new arity -- among those =< D
  % D limits how much size we have: cannot grow larger,
  member_choice(Arity,GoodNs),Last is Arity-1,  
  N2 is N1+Arity,
  between_choice(0,Last,K), % fill out with leaves except for K where A links
  add_leaves(0,Arity,K,A,Es,OtherEs).
  
% extends with leaves seen as unbound variables 
add_leaves(N,N,_,_)-->[].
add_leaves(I,N,K,A)-->{I<N,I=:=K,I1 is I+1},add_leaves(I1,N,K,A).
add_leaves(I,N,K,A)-->{I<N,I=\=K,I1 is I+1},[e(N,I,A,_)],add_leaves(I1,N,K,A).  



extend_to(M,NFs,Root,NewEs):-
  init_funs(NFs,Ns,Root,Es),
  length(Es,N),
  extension_loop(Ns,Es,NewEs,N,M).
 
extension_loop(_,Es,Es,N,N).
extension_loop(Ns,Es,NewEs,N1,N3):-D is N3-N1,D>0,
  filter_smaller(Ns,D,GoodNs),
  extension_step(GoodNs,Es,EsSoFar,N1,N2),
  extension_loop(GoodNs,EsSoFar,NewEs,N2,N3).
 
filter_smaller([],_,[]).
filter_smaller([I|_Is],D,[]):-I>D. % ok as they are sorted
filter_smaller([I|Is],D,[I|Js]):-I=<D,filter_smaller(Is,D,Js).


ext_test(M,CFs,Root-Edges):-classify_funs(CFs,_,NFs),extend_to(M,NFs,Root,Edges).

% building a term from the list of edges

% labeling vertices with concrete function synbols and constants
edges2term(Cs,NFs,Xs):-maplist(edge2fun(NFs),Xs),maplist(leaf2constant(Cs),Xs).

% constants are added at leafs where unbound vars are found
leaf2constant(Cs,e(_,_,_,Leaf)):-member_choice(C,Cs),(Leaf=C->true;true).

% select among funs of matching arity ###

%edge2fun(A,B):-ppp(A->B),fail.
edge2fun(NFs,e(N,I,T,A)):-
  I1 is I+1,
  member(N-Fs,NFs),
  (var(T)->member_choice(F,Fs);true),
  functor(T,F,N),
  arg(I1,T,A).

% generator for a multiset of terms
gen_terms(M,FCs,T):-
  classify_funs(FCs,Cs,NFs), 
  extend_to(M,NFs,T,Es),
  edges2term(Cs,NFs,Es).

% generator for a set of terms
gen_term(M,FCs,T):-distinct(T,gen_terms(M,FCs,T)).


