% ICLP'15 technical communication
:-use_module(library(lists)).
% :-ensure_loaded(lamtools).

dbTermSize(v(_),0).
dbTermSize(l(A),R):-
  dbTermSize(A,RA),
  R is RA+1.
dbTermSize(a(A,B),R):-
  dbTermSize(A,RA),
  dbTermSize(B,RB),
  R is 1+RA+RB.

isClosed(T):-isClosed1(T,0).

isClosed1(v(N),D):-N<D.
isClosed1(l(A),D):-D1 is D+1,
  isClosed1(A,D1).
isClosed1(a(X,Y),D):-
  isClosed1(X,D),
  isClosed1(Y,D).

boundTypeOf(v(I),V,Vs):-
  nth0(I,Vs,V0),
  unify_with_occurs_check(V,V0).
boundTypeOf(a(A,B),Y,Vs):-
  boundTypeOf(A,(X->Y),Vs),
  boundTypeOf(B,X,Vs).
boundTypeOf(l(A),(X->Y),Vs):-
  boundTypeOf(A,Y,[X|Vs]).

boundTypeOf(A,T):-boundTypeOf(A,T0,[]),bindType(T0),!,T=T0.

bindType(o):-!.
bindType((A->B)):-
  bindType(A),
  bindType(B).

motzkinTree(L,Tree):-motzkinTree(Tree,L,0).

motzkinTree(u)-->down.
motzkinTree(l(A))-->down,motzkinTree(A).
motzkinTree(a(A,B))-->down,
  motzkinTree(A),
  motzkinTree(B).

down(From,To):-From>0,To is From-1.   

genDBterm(v(X),V)-->
  {down(V,V0)},
  {between(0,V0,X)}.
genDBterm(l(A),V)-->down,
  {up(V,NewV)},
  genDBterm(A,NewV).
genDBterm(a(A,B),V)-->down,
  genDBterm(A,V),
  genDBterm(B,V).  

up(K1,K2):-K2 is K1+1.

genDBterm(L,T):-genDBterm(T,0,L,0).

genDBterms(L,T):-genDBterm(T,0,L,_).

genTypedTerm1(L,Term,Type):-
  genDBterm(L,Term),
  boundTypeOf(Term,Type).

genTypedTerms1(L,Term,Type):-
  genDBterms(L,Term),
  boundTypeOf(Term,Type).

genTypedTerm(v(I),V,Vs)-->
  {
   nth0(I,Vs,V0),
   unify_with_occurs_check(V,V0)
  }.
genTypedTerm(a(A,B),Y,Vs)-->down,
  genTypedTerm(A,(X->Y),Vs),
  genTypedTerm(B,X,Vs).
genTypedTerm(l(A),(X->Y),Vs)-->down,
  genTypedTerm(A,Y,[X|Vs]).  

genTypedTerm(L,B,T):-
  genTypedTerm(B,T,[],L,0),
  bindType(T).

genTypedTerms(L,B,T):-
  genTypedTerm(B,T,[],L,_),
  bindType(T).

queryTypedTerm(L,QueryType,Term):-
  genTypedTerm(L,Term,QueryType),
  boundTypeOf(Term,QueryType).

queryTypedTerms(L,QueryType,Term):-
  genTypedTerms(L,Term,QueryType),
  boundTypeOf(Term,QueryType).

typeSiblingOf(Term,Sibling):-
  dbTermSize(Term,L),
  boundTypeOf(Term,Type),
  queryTypedTerms(L,Type,Sibling).

countForType(GivenType,M,Rs):-
  findall(R,
    (
       between(1,M,L),sols(queryTypedTerm(L,GivenType,_B),R)
    ),
  Rs).  

genTypedWithSomeFree(Size,NbFree,B,T):-
   between(0,NbFree,NbVs),
   length(FreeVs,NbVs),
   genTypedTerm(B,T,FreeVs,Size,0),
   bindType(T).

typeCountsFor(L,T:Count):-
  setof(X,genTypedTerm(L,X,T),Xs),
  length(Xs,Count).
  
typeCountsUpTo(L,T:Count):-
  setof(X,genTypedTerms(L,X,T),Xs),
  length(Xs,Count).
  
popularTypesFor(L,K,[Difs,Sols,Ratio],PopularTs):-
  sols(genTypedTerm(L,_,_),Sols),
  setof(Count-T,typeCountsFor(L,T:Count),KTs),
  reverse(KTs,Sorted),
  take(K,Sorted,PopularTs),
  length(KTs,Difs),
  Ratio is Difs/Sols.

popularTypesUpTo(L,K,[Difs,Sols,Ratio],PopularTs):-
  sols(genTypedTerms(L,_,_),Sols),
  setof(Count-T,typeCountsUpTo(L,T:Count),KTs),
  reverse(KTs,Sorted),
  take(K,Sorted,PopularTs),
  length(KTs,Difs),
  Ratio is Difs/Sols.
  
take(0,_Xs,[]):-!.
take(_,[],[]):-!.
take(N,[X|Xs],[X|Ys]):-N>0,N1 is N-1,take(N1,Xs,Ys). 
 
countWithFree(M,K,Rs):-
  findall(R,
    (
       between(1,M,L),sols(genTypedWithSomeFree(L,K,_B,_T),R)
    ),
  Rs).   

genType(o)-->[].
genType((X->Y))-->down,
  genType(X),
  genType(Y). 

genType(N,X):-genType(X,N,0).

genTypes(N,X):-genType(X,N,_).

genByType(L,B,T):-
  genType(L,T),
  queryTypedTerms(L,T,B).

countByType(M,Rs):-
  findall(R,
    (
       between(1,M,L),sols(genByType(L,_B,_T),R)
    ),
  Rs).

% helpers

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

count2(F,M,Ks):-findall(K,(between(1,M,L),sols(call(F,L,_),K)),Ks).

count3(F,M,Ks):-findall(K,(between(1,M,L),sols(call(F,L,_,_),K)),Ks).


