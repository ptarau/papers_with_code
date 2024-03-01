% random lambda terms: decorate Motzkin trees

nat2probs(0,[]).
nat2probs(N,Ps):-N>0,
  Sum is 1-1/2^N,
  Last is 1-Sum,
  Inc is Last/N, % writeln(Last->Inc),
  make_probs(N,Inc,1,Ps).

make_probs(0,_,_,[]).
make_probs(K,Inc,P0,[P|Ps]):-
  K>0,K1 is K-1,P1 is P0/2, P is P1+Inc,
  make_probs(K1,Inc,P1,Ps).

walk_probs([P|Ps],K1,K3):-random(X),X<P,!,K2 is K1+1,walk_probs(Ps,K2,K3).
walk_probs(_,K,K).

decorate(v,0,X)-->[X]. % free variable
decorate(v,N,K)-->{N>0,nat2probs(N,Ps),walk_probs(Ps,0,K)},[].
decorate(l(X),N,l(Y))-->{N1 is N+1},decorate(X,N1,Y).
decorate(a(X,Y),N,a(A,B))-->decorate(X,N,A),decorate(Y,N,B).

plain_gen(N,T,FreeVars):-mot_gen(N,B),decorate(B,0,T,FreeVars,[]).

decorate_to_closed(B,T):-decorate(B,0,T,[],[]).

try_closed(N,T):-mot_gen(N,B),decorate_to_closed(B,T).


% when no answer is found, try a fresh restart
try_gen(Gen,Lim,I,J):-
  I<Lim,
  ( % use multiple try if-then-else, do the else only if cond. has no answers
    call(Gen)*->J=I
  ; I1 is I+1,
    try_gen(Gen,Lim,I1,J)
  ).

closed_gen(N,T,I):- Lim is 100+2^min(N,24),try_gen(try_closed(N,T),Lim,0,I).

% all terms lambda term generator

lamb(I,L)-->{L1 is L-1,between(0,L1,I)}.
lamb(l(A),L)-->{NewL is L+1},spend(1),lamb(A,NewL). 
lamb(a(A,B),L)-->spend(2),lamb(A,L),lamb(B,L).

% A135501: closed lambda-terms of size n and size 1 for the variables
closed_lamb(N,T):-lamb(T,0,N,0).

% type inference step
type_of(X,T):-type_of(X,T,[]).

type_of(I,V,Vs):-integer(I),
  nth0(I,Vs,V0),
  unify_with_occurs_check(V,V0).
type_of(l(A),(X->Y),Vs):-
  type_of(A,Y,[X|Vs]). 
type_of(a(A,B),Y,Vs):-
  type_of(A,(X->Y),Vs),
  type_of(B,X,Vs).

%%%%%%%% ?
mtype_of(X,T):-mtype_of(X,T,[]).

mtype_of(v,Vs,Vs).
mtype_of(l(A),(X->Y),Vs):-
  mtype_of(A,Y,[X|Vs]). 
mtype_of(a(A,B),Y,Vs):-
  mtype_of(A,(X->Y),Vs),
  mtype_of(B,X,Vs).


% A220471 if size of vars 0 i.e. a/2 spends 1 instead of 2
typed_lamb(N,Term,Type):-closed_lamb(N,Term),type_of(Term,Type).  

try_typed(N,T,Type):-mot_gen(N,B),decorate_to_closed(B,T),type_of(T,Type).

typed_gen(N,T,Type,steps(Steps),size(Size)):- 
  Lim is 100+2^min(N,24),
  try_gen(try_typed(N,T,Type),Lim,0,Steps),
  tsize(T,Size).
  
% natural size of a term, countin variable N as having size N
tsize(N,S):-integer(N),S=N.
tsize(l(X),S):-tsize(X,S1),S is S1+1.
tsize(a(X,Y),S):-tsize(X,S1),tsize(Y,S2),S is S1+S2+2.


fast_typed_gen(N,T,Type,steps(Steps),size(Size)):- 
  Lim is 100+2^min(N,24),
  try_gen(try_typed(N,T,Type),Lim,0,Steps),
  tsize(T,Size).
  
decorate_to_typed(Mot,Term,Type):-decotype(Mot,0,Term,Type,[],[]).

decotype(v,Ts,V,T)-->{nth0(V,Ts,T0),unify_with_occurs_check(T,T0)}.
decotype(l(X),Ts,l(Y),S->T)-->decotype(X,[S|Ts],Y,T).
decotype(a(X,Y),N,a(A,B),T)-->decotype(X,N,A,S->T),decotype(Y,N,B,S).


% 0.3341408333975344
% 0.667473848839429

% Boltzmann sampler for Motzkin trees

rmot(N,Term):-rmot(N,Term,_I).

rmot(N,Term,I+S):-N1 is N+N//10,rmot(12345678,N,N1,I,Term,S).

rmot(Times,Min,Max,I,Term,Size):-
  between(1,Times,I),
  mot_in_range(Min,Max,Term,Size),
  !. 

mot_in_range(Min,Max,X,Size):-
  Delta is Max-Min,
  motR(X,Max,Dif),
  Dif=<Delta,
  !,
  Size is Max-Dif.


motR(X,S1,S2):-random(R),motR(R,X,S1,S2).

motR(R,v,S,S):-R<0.3341408333975344,!.
motR(R,l(X),S1,S3):-S1>0,R<0.667473848839429,!,
  S2 is S1-1,
  motR(X,S2,S3).
motR(_,a(X,Y),S1,S4):-S1>1,
  S2 is S1-2,
  motR(X,S2,S3),
  motR(Y,S3,S4).

typed_from_rmot(N,Term,Type):-
  rmot(N,B),
  decorate_to_closed(B,Term),
  type_of(Term,Type).

deco_typed_gen(N,T,Type,steps(Steps),size(Size)):- 
  Lim is 100+2^min(N,24),
  try_gen(typed_from_rmot(N,T,Type),Lim,0,Steps),
  tsize(T,Size).



ccl(N):-ncounts(N,closed_lamb(_,_)).
bcl(N):-ntimes(N,closed_lamb(_,_)).
scl(N):-nshow(N,closed_lamb(_,_)). 
pcl(N):-npp(N,closed_lamb(_,_)). 

ctl(N):-ncounts(N,typed_lamb(_,_,_)).
btl(N):-ntimes(N,typed_lamb(_,_,_)).
stl(N):-nshow(N,typed_lamb(_,_,_)). 
ptl(N):-npp(N,typed_lamb(_,_,_)). 
  
cml(N):-ncounts(N,plain_gen(_,_,_)).
bml(N):-ntimes(N,plain_gen(_,_,_)).
sml(N):-nshow(N,plain_gen(_,_,_)). 
pml(N):-npp(N,plain_gen(_,_,_)). 

cmc(N):-ncounts(N,closed_gen(_,_,_)).
bmc(N):-ntimes(N,closed_gen(_,_,_)).
smc(N):-nshow(N,closed_gen(_,_,_)). 
pmc(N):-npp(N,closed_gen(_,_,_)). 

cmt(N):-ncounts(N,typed_gen(_,_,_,_,_)).
bmt(N):-ntimes(N,typed_gen(_,_,_,_,_)).
smt(N):-nshow(N,typed_gen(_,_,_,_,_)). 
pmt(N):-npp(N,typed_gen(_,_,_,_,_)). 


fl1(N):-nct(N,closed_lamb(_,_)).
fl2(N):-nct(N,typed_lamb(_,_,_)).
fl3(N):-nct(N,mot_gen(_,_)).
fl4(N):-nct(N,plain_gen(_,_,_)).
fl5(N):-nct(N,closed_gen(_,_,_)).
fl6(N):-nct(N,typed_gen(_,_,_,_,_)).


