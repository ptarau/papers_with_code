:-use_module(library(lists)).
:-use_module(library(apply)).
% :-ensure_loaded(lamtools).

genSK(k)-->[].
genSK(s)-->[].
genSK(X*Y)-->down,genSK(X),genSK(Y).

down(From,To):-From>0,To is From-1.  

genSK(N,X):-genSK(X,N,0).

genSKs(N,X):-genSK(X,N,_).

csize(k,0).
csize(s,0).
csize((X*Y),S):-csize(X,A),csize(Y,B),S is 1+A+B.

eval(k,k).
eval(s,s). 
eval(F*G,R):-eval(F,F1),eval(G,G1),app(F1,G1,R).


app((s*X)*Y,Z,R):-!,  % S
  app(X,Z,R1),
  app(Y,Z,R2),
  app(R1,R2,R).
app(k*X,_Y,R):-!,R=X. % K  
app(F,G,F*G).

kB(l(l(v(1)))).

sB(l(l(l(a(a(v(2),v(0)),a(v(1),v(0))))))).

c2b(s,S):-sB(S).
c2b(k,K):-kB(K).
c2b((X*Y),a(A,B)):-c2b(X,A),c2b(Y,B).

skTypeOf(k,(A->(_B->A))).  
skTypeOf(s,(((A->B->C)-> (A->B)->A->C))).
skTypeOf(A*B,Y):-
  skTypeOf(A,T),
  skTypeOf(B,X),
  unify_with_occurs_check(T,(X->Y)).

simpleTypeOf(A,T):-skTypeOf(A,T),bindWithBaseType(T).

bindWithBaseType(o):-!. % bind all variables with type 'o'
bindWithBaseType((A->B)):-bindWithBaseType(A),bindWithBaseType(B).

typable(X):-skTypeOf(X,_).

genTypedSK(L,X,T):-genSK(L,X),simpleTypeOf(X,T).

genUntypableSK(L,X):-genSK(L,X),\+skTypeOf(X,_).

cat(0,1).
cat(N,R):-N>0, PN is N-1,cat(PN,R1),R is 2*(2*N-1)*R1//(N+1).

countTyped(L,Typed,SKs,Prop):-
  sols(genTyped(L,_,_),Typed),
  cat(L,Cats),SKs is 2^(L+1)*Cats,
  Prop is Typed/SKs.
  
tcounts:-
  between(0,9,I),countTyped(I,Typed,All,Prop),
  write((I,&,Typed,&,All,&,Prop)),nl,fail.

genType(o)-->[].
genType((X->Y))-->down,genType(X),genType(Y). 

genType(N,X):-genType(X,N,0).

genTypes(N,X):-genType(X,N,_).

genByTypeSK(L,X,T):-
  genType(L,T),
  genSKs(L,X),
  simpleTypeOf(X,T).

tsize(V,R):-var(V),!,R=0.
tsize(A,0):-atomic(A),!.
tsize((X*Y),R):-tsize(X,R1),tsize(Y,R2),R is 1+R1+R2. 
tsize((X->Y),R):-tsize(X,R1),tsize(Y,R2),R is 1+R1+R2. 

queryByTypeSK(L,X,T):-queryByType(X,T,L,0),simpleTypeOf(X,T).

queryByTypeSKs(L,X,T):-queryByType(X,T,L,_),simpleTypeOf(X,T).

queryByType(k,(A->(_B->A)))-->[]. 
queryByType(s,(((A->B->C)-> (A->B)->A->C)))-->[].
queryByType((A*B),Y)-->
  down,
  queryByType(A,T),
  queryByType(B,X),
  {unify_with_occurs_check(T,(X->Y))}.

xgenByTypeSK(L,X,T):-
  genType(L,T),
  queryByTypeSKs(L,X,T).  

countByType(M,Rs):-
  findall(R,
    (
       between(1,M,L),sols(genByTypeSK(L,_B,_T),R)
    ),
  Rs).

wellTypedFrontier(Term,Trunk,FrontierEqs):-wtf(Term, Trunk,FrontierEqs,[]).

wtf(Term,X)-->{typable(Term)},!,[X=Term].
wtf(A*B,X*Y)-->wtf(A,X),wtf(B,Y).

fuseFrontier(FrontierEqs):-maplist(call,FrontierEqs).

extractFrontier(FrontierEqs,Frontier):-maplist(arg(2),FrontierEqs,Frontier).



simplifySK(Term,Trunk):-
  wellTypedFrontier(Term,Trunk,FrontierEqs),
  extractFrontier(FrontierEqs,Fs),
  maplist(eval,Fs,NormalizedFs),
  maplist(arg(1),FrontierEqs,Vs),
  Vs=NormalizedFs.

uselessTypeOf(k,(A->(_B->A))).
uselessTypeOf(s,(((A->B->C)-> (A->B)->A->C))).
uselessTypeOf((A*B),Y):-uselessTypeOf(A,(X->Y)),uselessTypeOf(B,X).

notReallyTypable(X):-uselessTypeOf(X,_).

sameAsAny(L,M):-genSK(L,M),notReallyTypable(M).

