% CICM'15 Calculemus
:-use_module(library(lists)).
:-use_module(library(apply)).

b2l(DeBruijnTerm,LambdaTerm):-b2l(DeBruijnTerm,LambdaTerm,_Vs).

b2l(v(I),V,Vs):-nth0(I,Vs,V).
b2l(a(A,B),a(X,Y),Vs):-b2l(A,X,Vs),b2l(B,Y,Vs).
b2l(l(A),l(V,Y),Vs):-b2l(A,Y,[V|Vs]).

l2b(StandardTerm,DeBruijnTerm):-copy_term(StandardTerm,Copy),
  numbervars(Copy,0,_),l2b(Copy,DeBruijnTerm,_Vs).

l2b('$VAR'(V),v(I),Vs):-once(nth0(I,Vs,'$VAR'(V))).
l2b(a(X,Y),a(A,B),Vs):-l2b(X,A,Vs),l2b(Y,B,Vs).
l2b(l(V,Y),l(A),Vs):-l2b(Y,A,[V|Vs]).

b2c(v(X),v(0,X)). 
b2c(a(X,Y),a(0,A,B)):-b2c(X,A),b2c(Y,B). 
b2c(l(X),R):-b2c1(1,X,R).

b2c1(K,a(X,Y),a(K,A,B)):-b2c(X,A),b2c(Y,B).
b2c1(K, v(X),v(K,X)).
b2c1(K,l(X),R):-up(K,K1),b2c1(K1,X,R).  

up(From,To):-From>=0,To is From+1.

c2b(v(K,X),R):-X>=0,iterLam(K,v(X),R).
c2b(a(K,X,Y),R):-c2b(X,A),c2b(Y,B),iterLam(K,a(A,B),R).

iterLam(0,X,X).
iterLam(K,X,l(R)):-down(K,K1),iterLam(K1,X,R).

down(From,To):-From>0,To is From-1. 

c2l --> c2b,b2l.

l2c --> l2b,b2c.

isClosed(T):-isClosed(T,0).
isClosed(v(K,N),S):-N<S+K.
isClosed(a(K,X,Y),S1):-S2 is S1+K,isClosed(X,S2),isClosed(Y,S2).

extractType(_:TX,TX):-!.
extractType(l(_:TX,A),(TX->TA)):-
  extractType(A,TA).
extractType(a(A,B),TY):-
  extractType(A,(TX->TY)),
  extractType(B,TX).

hasType(CTerm,ExtractedType):-
  c2l(CTerm,LTerm),
  extractType(LTerm,ExtractedType),
  acyclic_term(LTerm),
  bindType(ExtractedType).

bindType(o):-!.
bindType((A->B)):-bindType(A),bindType(B).  

typeable(Term):-hasType(Term,_Type).

genTypedB(v(I),V,Vs)-->
  { 
    nth0(I,Vs,V0),
    unify_with_occurs_check(V,V0)
  }.
genTypedB(a(A,B),Y,Vs)-->down,
  genTypedB(A,(X->Y),Vs),
  genTypedB(B,X,Vs).
genTypedB(l(A),(X->Y),Vs)-->down,
  genTypedB(A,Y,[X|Vs]). 

genTypedB(L,B,T):-genTypedB(B,T,[],L,0),bindType(T).

genTypedBs(L,B,T):-genTypedB(B,T,[],L,_),bindType(T).

queryTypedB(L,Term,QueryType):-
  genTypedB(L,Term,Type),
  Type=QueryType.

catpar(T,Ps):-catpar(T,0,1,Ps,[]).
catpar(X,L,R) --> [L],catpars(X,L,R).
catpars(o,_,R) --> [R].
catpars((X->Xs),L,R)-->catpar(X,L,R),catpars(Xs,L,R). 

rankCatalan(Xs,R):-
  length(Xs,XL),XL>=2, 
  L is XL-2, I is L // 2,
  localRank(I,Xs,N),
  S is 0, PI is I-1,
  rankLoop(PI,S,NewS),
  R is NewS+N.

unrankCatalan(R,Xs):- 
  S is 0, I is 0,
  unrankLoop(R,S,I,NewS,NewI),
  LR is R-NewS, 
  L is 2*NewI+1,
  length(As,L),
  localUnrank(NewI,LR,As),
  As=[_|Bs], 
  append([0|Bs],[1],Xs).

rankType(T,Code):-
  catpar(T,Ps),
  rankCatalan(Ps,Code).
  
unrankType(Code,Term):-
  unrankCatalan(Code,Ps),
  catpar(Term,Ps).

cskel(S,Vs, T):-cskel(T,S,Vs,[]).

cskel(v(K,N),o)-->[K,N].
cskel(a(K,X,Y),(A->B))-->[K],cskel(X,A),cskel(Y,B).

toSkel(T,Skel,Vs):-
  cskel(T,Cat,Vs,[]),
  catpar(Cat,Skel).
  
fromSkel(Skel,Vs, T):-
  catpar(Cat,Skel),
  cskel(T,Cat,Vs,[]).

fromCantorTuple(Ns,N):-
  list2set(Ns,Xs),
  fromKSet(Xs,N).

fromKSet(Xs,N):-untuplingLoop(Xs,0,0,N).

untuplingLoop([],_L,B,B).
untuplingLoop([X|Xs],L1,B1,Bn):-L2 is L1+1, 
  binomial(X,L2,B),B2 is B1+B,
  untuplingLoop(Xs,L2,B2,Bn).  

toKSet(K,N,Ds):-combinatoriallDigits(K,N,[],Ds).

combinatoriallDigits(0,_,Ds,Ds).
combinatoriallDigits(K,N,Ds,NewDs):-K>0,K1 is K-1,
  upperBinomial(K,N,M),M1 is M-1,
  binomial(M1,K,BDigit),N1 is N-BDigit,
  combinatoriallDigits(K1,N1,[M1|Ds],NewDs).

upperBinomial(K,N,R):-S is N+K,
  roughLimit(K,S,K,M),L is M // 2,
  binarySearch(K,N,L,M,R).

roughLimit(K,N,I, L):-binomial(I,K,B),B>N,!,L=I.
roughLimit(K,N,I, L):-J is 2*I,
  roughLimit(K,N,J,L).

binarySearch(_K,_N,From,From,R):-!,R=From.
binarySearch(K,N,From,To,R):-Mid is (From+To) // 2,binomial(Mid,K,B),
  splitSearchOn(B,K,N,From,Mid,To,R).

splitSearchOn(B,K,N,From,Mid,_To,R):-B>N,!,
  binarySearch(K,N,From,Mid,R).
splitSearchOn(_B,K,N,_From,Mid,To,R):-Mid1 is Mid+1,
  binarySearch(K,N,Mid1,To,R).  

toCantorTuple(K,N,Ns):-
  toKSet(K,N,Ds),
  set2list(Ds,Ns).

rankTerm(Term,Code):-
  toSkel(Term,Ps,Ns),
  rankCatalan(Ps,CatCode),
  fromCantorTuple(Ns,VarsCode),
  fromCantorTuple([CatCode,VarsCode],Code).

unrankTerm(Code,Term):-
  toCantorTuple(2,Code,[CatCode,VarsCode]),
  unrankCatalan(CatCode,Ps), 
  length(Ps,L2),L is (L2-2) div 2, L3 is 3*L+2,
  toCantorTuple(L3,VarsCode,Ns),
  fromSkel(Ps,Ns,Term).

ogen(M,T):-between(0,M,I),unrankTerm(I,T).  

cgen(M,IT):-ogen(M,IT),isClosed(IT).

tgen(M,IT):-cgen(M,IT),typeable(IT).

ranTerm(Filter,Bits,T):-X is 2^Bits,N is X+random(X),M is N+X,
  between(N,M,I),
   unrankTerm(I,T),call(Filter,T),
  !.

ranOpen(Bits,T):-ranTerm(=(_),Bits,T).  

ranClosed(Bits,T):-ranTerm(isClosed,Bits,T).

ranTyped(Bits,T):-ranTerm(closedTypeable,Bits,T).

closedTypeable(T):-isClosed(T),typeable(T).



% tests

go(A,R):-V1=v(3,4),V2=v(2,3),
    A1=a(2,V1,V2),
    A2=a(3,A1,V1),
    A=a(1,A2,A1),
    rankTerm(A,R),
    unrankTerm(R,B),
    A=B.
      
tshow(B):-  
  nl,write('---------'),nl,
  write(B),nl,
  b2l(B,X),
  lshow(X),
  fail.
  
lshow(X):-  
  p(X),nl,
  lamshow(X),nl,
  ( l2c(X,BX),hasType(BX,TX)->p(TX)
  ; write('!!! NOT typeable !!!')
  ),
  nl,
  fail.
lshow(_).  

% closed/open ratio

ccount(M,R):-sols(cgen(M,_),K),R is K/M.  


rgo:-rgo(200).


no1:-T=l(B,a(B,B)),nogo(T).
no2:-T=l(_,l(B,a(B,B))),nogo(T).


nogo(T):-
  lshow(T),
  fail.

rgo(M):-  
 ranClosed(M,C),
 c2l(C,T),
 c2b(C,B),
 pn(compressed=C),
 pn(deBruijn=B),
 tsize(C,S),
 nl,write(size=S),nl,
 lshow(T),
 fail.
  
tsize(v(K,_),K).
tsize(a(K,X,Y),Size):-tsize(X,A),tsize(Y,B),Size is A+B+K+1.    
    
%%%%%%%% helpers %%%%%%

p(T):- numbervars(T,0,_),write(T),fail;true.

pn(T):-p(T),nl.
 
ln(T):-lamshow(T),nl.
 
lamshow(T):-
  numbervars(T,0,_),
  lamshow(T,Cs,[]),
  maplist(write,Cs),
  fail.
lamshow(_).

lamshow('$VAR'(I))--> [x],[I].
lamshow('$VAR'(I):'$VAR'(J))--> 
  [x],[I],[(':')],[t],[J].
lamshow(v(I))-->[I].
lamshow(l(E))-->[('(\\')],lamshow(E),[(')')].
lamshow(l('$VAR'(I),E))-->[('(')],[('\\')],[x],[I],[('.')],lamshow(E),[(')')].
lamshow(l('$VAR'(I):'$VAR'(J),E))-->
   [('(')],[('\\')],[x],[I],[':'],[t],[J],[('.')],
   lamshow(E),[(')')].
lamshow(a(X,Y))-->[('(')],lamshow(X),[(' ')],lamshow(Y),[(')')].

texshow(T):-numbervars(T,0,_),texshow(T,Cs,[]),
  write('$'),
  maplist(write,Cs),
  write('$\\\\'),
  fail.
texshow(_).

texshow('$VAR'(I))--> [x],[I].
texshow(v(I))-->[I].
texshow(l(E))-->[('~\\lambda ')],texshow(E),[(' ')].
texshow(l('$VAR'(I),E))-->[(' ')],[('~\\lambda ')],[x],[I],[('.')],texshow(E),[(' ')].
texshow(a(X,Y))-->[('(')],texshow(X),[('~')],texshow(Y),[(')')].

gen(F,L,T):-call(F,L,T).

count(F,M,Ks):-findall(K,(between(1,M,L),sols(gen(F,L,_),K)),Ks).

% counts nb. of solutions of Goal 
sols(Goal, Times) :-
        Counter = counter(0),
        (   Goal,
            arg(1, Counter, N0),
            N is N0 + 1,
            nb_setarg(1, Counter, N),
            fail
        ;   arg(1, Counter, Times)
        ).


% some combinators

k(l(l(v(1)))).
s(l(l(l(a(a(v(2),v(0)),a(v(1),v(0))))))).
skk(a(a(l(l(l(a(a(v(2),v(0)),a(v(1),v(0)))))),l(l(v(1)))),l(l(v(1))))).
i(l(v(0))).
y(l(a(l(a(v(1),a(v(0),v(0)))),l(a(v(1),a(v(0),v(0))))))).
yi(a(l(a(l(a(v(1),a(v(0),v(0)))),l(a(v(1),a(v(0),v(0)))))),l(v(0)))).
zero(l(l(v(0)))).
one(l(l(a(v(1),v(0))))).

two(l(l(a(v(1), a(v(1), v(0)))))).
suc(l(l(l(a(v(1),a(a(v(2),v(1)),v(0))))))).
pre(l(l(l(a(a(a(v(2),l(l(a(v(0),a(v(1),v(3)))))),l(v(1))),l(v(0))))))).

iszero(l(a(a(v(0),l(l(l(v(0))))),l(l(v(1)))))).
true(l(l(v(1)))).
false(l(l(v(0)))).
ite(l(l(l(a(a(v(2),v(1)),v(0)))))).
pair(l(l(l(a(a(v(0),v(2)),v(1)))))).
first(l(a(v(0),l(l(v(1)))))).
second(l(a(v(0),l(l(v(0)))))).
add(l(l(l(l(a(a(v(3),v(1)),a(a(v(2),v(1)),v(0)))))))).
mul((l(l(l(a(a(v(2),a(v(3),v(1))),v(0))))))).
ack(l(a(a(a(v(0),l(l(a(v(1),a(a(v(0),v(1)),l(v(0))))))),l(l(l(a(v(1),a(a(v(2),v(1)),v(0))))))),v(0)))).


rco(F):-call(F,B),b2c(B,C),
  pn(F:C),
  rankTerm(C,R),unrankTerm(R,CC),
  pn(R),
  C=@=CC,
  pn(ok),
  fail.


cat(0,1).
cat(N,R):-N>0, PN is N-1, SN is N+1,cat(PN,R1),R is 2*(2*N-1)*R1//SN.

binDif(N,X,Y,R):- N1 is 2*N-X,R1 is N - (X + Y) // 2, R2 is R1-1,
  binomial(N1,R1,B1),binomial(N1,R2,B2),R is B1-B2.  

localRank(N,As,NewLo):- X is 1, Y is 0, Lo is 0,
  binDif(N,0,0,Hi0),Hi is Hi0-1,
  localRankLoop(As,N,X,Y,Lo,Hi,NewLo,_NewHi).

localRankLoop(As,N,X,Y,Lo,Hi,FinalLo,FinalHi):-N2 is 2*N,X< N2,!,
  PY is Y-1, SY is Y+1, nth0(X,As,A),
  (0=:=A-> binDif(N,X,PY,Hi1),
     NewHi is Hi-Hi1, NewLo is Lo, NewY is SY
   ; binDif(N,X,SY,Lo1),
     NewLo is Lo+Lo1, NewHi is Hi, NewY is PY
  ), NewX is X+1,
  localRankLoop(As,N,NewX,NewY,NewLo,NewHi,FinalLo,FinalHi).
localRankLoop(_As,_N,_X,_Y,Lo,Hi,Lo,Hi).  

rankLoop(I,S,FinalS):-I>=0,!,cat(I,C),NewS is S+C, PI is I-1,
  rankLoop(PI,NewS,FinalS).
rankLoop(_,S,S).

localUnrank(N,R,As):-Y is 0,Lo is 0,binDif(N,0,0,Hi0),Hi is Hi0-1, X is 1,
  localUnrankLoop(X,Y,N,R,Lo,Hi,As).

localUnrankLoop(X,Y,N,R,Lo,Hi,As):-N2 is 2*N,X=<N2,!,
   PY is Y-1, SY is Y+1,
   binDif(N,X,SY,K), LK is Lo+K,
   ( R<LK -> NewHi is LK-1, NewLo is Lo, NewY is SY, Digit=0
   ; NewLo is LK, NewHi is Hi, NewY is PY, Digit=1
   ),nth0(X,As,Digit),NewX is X+1,
   localUnrankLoop(NewX,NewY,N,R,NewLo,NewHi,As).
localUnrankLoop(_X,_Y,_N,_R,_Lo,_Hi,_As). 

unrankLoop(R,S,I,FinalS,FinalI):-cat(I,C),NewS is S+C, NewS=<R,
   !,NewI is I+1,
   unrankLoop(R,NewS,NewI,FinalS,FinalI).
unrankLoop(_,S,I,S,I).

list2set(Ns,Xs) :- list2set(Ns,-1,Xs).

list2set([],_,[]).
list2set([N|Ns],Y,[X|Xs]) :- 
  X is (N+Y)+1, 
  list2set(Ns,X,Xs).

set2list(Xs,Ns) :- set2list(Xs,-1,Ns).

set2list([],_,[]).
set2list([X|Xs],Y,[N|Ns]) :- 
  N is (X-Y)-1, 
  set2list(Xs,X,Ns).

binomialLoop(_,K,I,P,R) :- I>=K, !, R=P.
binomialLoop(N,K,I,P,R) :- I1 is I+1, P1 is ((N-I)*P) // I1,
   binomialLoop(N,K,I1,P1,R).

binomial(_N,K,R):- K<0,!,R=0.
binomial(N,K,R) :- K>N,!, R=0.
binomial(N,K,R) :- K1 is N-K, K>K1, !, binomialLoop(N,K1,0,1,R).
binomial(N,K,R) :- binomialLoop(N,K,0,1,R).

b2lK(K,DeBruijnTerm,LambdaTerm):-
  length(Vs,K),
  b2l(DeBruijnTerm,LambdaTerm,Vs).

