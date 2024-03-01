remy_init([e(left,A,_),e(right,A,_)]).

left_or_right(I,J):-choice_of(2,Dice),left_or_right(Dice,I,J).

choice_of(N,K):-K is random(N).
% choice_of(N,K):-N>0,N1 is N-1,between(0,N1,K).

left_or_right(0,left,right).
left_or_right(1,right,left).

grow(e(LR,A,B), e(LR,A,C),e(I,C,_),e(J,C,B)):-left_or_right(I,J).

remy_step(Es,NewEs,L,NewL):-NewL is L+2,choice_of(L,Dice),
  remy_step1(Dice,Es,NewEs).

remy_step1(0,[U|Xs],[X,Y,Z|Xs]):-grow(U, X,Y,Z).
remy_step1(D,[A|Xs],[A|Ys]):-D>0,D1 is D-1,remy_step1(D1,Xs,Ys).

remy_loop(0,[],0).
remy_loop(1,Es,2) :-remy_init(Es).
remy_loop(K,NewEs,N3):-K>1, K1 is K-1,remy_loop(K1,Es,N2),
  remy_step(Es,NewEs,N2,N3).

bind_nodes([],v).
bind_nodes([X|Xs],Root):-X=e(_,Root,_),
  maplist(bind_internal,[X|Xs]),
  maplist(bind_leaf,[X|Xs]).

bind_internal(e(left,a(A,_),A)).
bind_internal(e(right,a(_,B),B)).

bind_leaf(e(_,_,Leaf)):-Leaf=v->true;true.

remy_term(K,B):-remy_loop(K,Es,0,_),bind_nodes(Es,B).

spend(Fuel,From,To):-From>=Fuel,To is From-Fuel.

gen(Fs,T)-->{member(F/K,Fs)},gen_cont(K,F,Fs,T).

gen_cont(0,F,_,F)-->[].
gen_cont(K,F,Fs,T)-->{K>0},spend(K),{functor(T,F,K)},gens(Fs,0,K,T).

gens(_,N,N,_)-->[].
gens(Fs,I,N,T)-->{I1 is I+1,arg(I1,T,A)},gen(Fs,A),gens(Fs,I1,N,T).

gen(N,Fs, T):-gen(Fs,T,N,0).

member_choice(Choice,Choices):-length(Choices,L),L>0,
  I is random(L),nth0(I,Choices,Choice).
select_choice(Choice,Choices,ChoicesLeft):-length(Choices,L),L>0,
  I is random(L),nth0(I,Choices,Choice,ChoicesLeft).
between_choice(From,To,Choice):-D is To-From+1,Choice is From+random(D).

classify_funs(FNs,Cs,SortedFs):-
 findall(N-F, member(F/N,FNs), NFs),sort(NFs,Ordered),
 group_pairs_by_key(Ordered,ByArityFs),
 keysort(ByArityFs,[0-Cs|SortedFs]).

get_arities(NFs,Ns):-maplist(arg(1),NFs,Ns).

init_funs(NFs,Ns,Root,Es):-get_arities(NFs,Ns),member_choice(N,Ns),
  init_fun(Root,N,Es).

init_fun(Root,N,Es):-N>0,length(Ns,N),N1 is N-1,numlist(0,N1,Is),
  maplist(=(N),Ns),maplist(make_edge(Root),Ns,Is,Es).

make_edge(X,N,I, e(N,I,X,_)).  


extension_step(GoodNs,OldEs,[e(M,I,X, A),e(Arity,K,A,Y)|Es],N1,N2):-
  GoodNs=[_|_],select_choice(e(M,I,X, Y),OldEs,OtherEs),
  member_choice(Arity,GoodNs),Last is Arity-1,N2 is N1+Arity,
  between_choice(0,Last,K), 
  add_leaves(0,Arity,K,A,Es,OtherEs).

add_leaves(N,N,_,_)-->[].
add_leaves(I,N,K,A)-->{I<N,I=:=K,I1 is I+1},add_leaves(I1,N,K,A).
add_leaves(I,N,K,A)-->{I<N,I=\=K,I1 is I+1},[e(N,I,A,_)],
  add_leaves(I1,N,K,A).  

extend_to(M,NFs,Root,NewEs):-init_funs(NFs,Ns,Root,Es),length(Es,N),
  extension_loop(Ns,Es,NewEs,N,M).

extension_loop(_,Es,Es,N,N).
extension_loop(Ns,Es,NewEs,N1,N3):-D is N3-N1,D>0,
  filter_smaller(Ns,D,GoodNs),
  extension_step(GoodNs,Es,EsSoFar,N1,N2),
  extension_loop(GoodNs,EsSoFar,NewEs,N2,N3).

filter_smaller([],_,[]).
filter_smaller([I|_Is],D,[]):-I>D. % ok as they are sorted
filter_smaller([I|Is],D,[I|Js]):-I=<D,filter_smaller(Is,D,Js).

ext_test(M,CFs, Root-Edges):-classify_funs(CFs,_,NFs),
  extend_to(M,NFs,Root,Edges).

edges2term(Cs,NFs,Xs):-
  maplist(edge2fun(NFs),Xs),maplist(leaf2constant(Cs),Xs).

edge2fun(NFs,e(N,I,T,A)):-I1 is I+1,member(N-Fs,NFs),
  (var(T)->member_choice(F,Fs);true),
  functor(T,F,N),arg(I1,T,A).

leaf2constant(Cs,e(_,_,_,Leaf)):-member_choice(C,Cs),(Leaf=C->true;true).

gen_terms(M,FCs,T):-classify_funs(FCs,Cs,NFs), 
  extend_to(M,NFs,T,Es),edges2term(Cs,NFs,Es).

gen_term(M,FCs,T):-distinct(T,gen_terms(M,FCs,T)).

mot_funs([v/0,l/1,a/2]).

mot(N,T):-mot_funs(CFs),gen(N,CFs,T).

sk_funs([s/0,k/0,a/2]).

gram_funs([t/0,e/0,left_arrow/2,right_arrow/2]).

nat2probs(0,[]).
nat2probs(N,Ps):-N>0,Sum is 1-1/2^N,Last is 1-Sum,Inc is Last/N,
  make_probs(N,Inc,1,Ps).

make_probs(0,_,_,[]).
make_probs(K,Inc,P0,[P|Ps]):-K>0,K1 is K-1,P1 is P0/2, P is P1+Inc,
  make_probs(K1,Inc,P1,Ps).

walk_probs([P|Ps],K1,K3):-random(X),X<P,!,K2 is K1+1,walk_probs(Ps,K2,K3).
walk_probs(_,K,K).

decorate(v,0,X)-->[X]. % free variable
decorate(v,N,K)-->{N>0,nat2probs(N,Ps),walk_probs(Ps,0,K)},[].
decorate(l(X),N,l(Y))-->{N1 is N+1},decorate(X,N1,Y).
decorate(a(X,Y),N,a(A,B))-->decorate(X,N,A),decorate(Y,N,B).

plain_gen(N,T,FreeVars):-mot_gen(N,B),decorate(B,0,T,FreeVars,[]).

closed_gen(N,T,I):- Lim is 100+2^min(N,24),try_closed_gen(Lim,0,I,N,T).

try_closed_gen(Lim,I,J,N,T):- I<Lim,
  ( mot_gen(N,B),decorate(B,0,T,[],[])*->J=I
  ; I1 is I+1, try_closed_gen(Lim,I1,J,N,T)
  ).

