% Remy's algorithm with focus on edges, in Prolog

:-include('stats.pro').

c:-['remy.pro'].

% simple binary tree generator

bt(v)-->step.
bt(a(X,Y))-->step,bt(X),bt(Y).

step(s(N),N).

% borrowed from https://github.com/maciej-bendkowski/boltzmann-brain
% generator for binary.in with default epsilon values
boltz(0.5007072019510743). 

boltz_bt(T,Size):-random(R),boltz_branch(R,T,Size).

boltz_branch(R,T,0):-boltz(B),R<B,!,T=v.
boltz_branch(_,a(X,Y),Size):-boltz_bt(X,S1),boltz_bt(Y,S2),Size is 1+S1+S2.

ran_bt(N,T):-
  M is N^2,
  between(1,M,_),
  boltz_bt(T,Size),
  % writeln(Size),
  Size>N,
  Size<2*N,
  !.

% boltzmann sampler for expected size 500
go_bt:-ran_bt(500,T),writeln(T),fail;true.

% generation


remy_init([e(left,A,_),e(right,A,_)]).

left_or_right(I,J):-choice_of(2,Dice),left_or_right(Dice,I,J).

choice_of(N,K):-N>0,K is random(N).

%choice_of(N,K):-N>0,N1 is N-1,between(0,N1,K).

left_or_right(0,left,right).
left_or_right(1,right,left).


grow(e(LR,A,B), e(LR,A,C),e(I,C,_),e(J,C,B)):-left_or_right(I,J).


remy_step(Es,NewEs,L,NewL):-NewL is L+2,
  choice_of(L,Dice),
	remy_step1(Dice,Es,NewEs).

remy_step1(0,[U|Xs],[X,Y,Z|Xs]):-grow(U, X,Y,Z).
remy_step1(D,[A|Xs],[A|Ys]):-D>0,D1 is D-1,remy_step1(D1,Xs,Ys).

remy_loop(0,[],N,N).
remy_loop(1,Es,N1,N2):-N2 is N1+2,remy_init(Es).
remy_loop(K,NewEs,N1,N3):-K>1,K1 is K-1,
  remy_loop(K1,Es,N1,N2),
  remy_step(Es,NewEs,N2,N3).

% binding nodes to build tree
bind_nodes([],v).
bind_nodes([X|Xs],Root):-X=e(_,Root,_),
  maplist(bind_internal,[X|Xs]),
  maplist(bind_leaf,[X|Xs]).

bind_internal(e(left,a(A,_),A)).
bind_internal(e(right,a(_,B),B)).

bind_leaf(e(_,_,Leaf)):-Leaf=v->true;true.

% multiset, when generating
remy_term(K,B):-remy_loop(K,Es,0,_),bind_nodes(Es,B).

% set of distinct terms, when generating
remy_gen(K,B):-distinct(B,remy_term(K,B)).

% tests and stats

r1:-time(remy_gen(4000,R)),writeln(R),fail.

t1:-sct(12,remy_gen(_,_)).

e2:-remy_gen(20,T),ppt(T),fail;true.

go:-go(6).
go(N):-cr(N),rc(N).

ca(N):-ncounts(N,remy_term(_,_)).
ba(N):-ntimes(N,remy_term(_,_)).
sa(N):-nshow(N,remy_term(_,_)). 

cr(N):-ncounts(N,remy_gen(_,_)).
br(N):-ntimes(N,remy_gen(_,_)).
sr(N):-nshow(N,remy_gen(_,_)). 
pr(N):-npp(N,remy_gen(_,_)).

% functor counts

rc(N):-nct(N,remy_term(_,_)).
rg(N):-nct(N,remy_gen(_,_)).

