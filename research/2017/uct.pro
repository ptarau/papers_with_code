:-include('lpgen/stats.pro').

closedTerm(N,X):-closedTerm(X,0,N,0).

closedTerm(v(I),V)-->{V>0,V1 is V-1,between(0,V1,I)}.
closedTerm(l(A),V)-->l,{succ(V,NewV)},closedTerm(A,NewV).  
closedTerm(a(A,B),V)-->a,closedTerm(A,V),closedTerm(B,V).

l(SX,X):-succ(X,SX).
a-->l,l.

toMotSkel(v(_),v).
toMotSkel(l(X),l(Y)):-toMotSkel(X,Y).
toMotSkel(a(X,Y),a(A,B)):-toMotSkel(X,A),toMotSkel(Y,B).

motSkel(N,X):-motSkel(X,N,0).

motSkel(v)-->[].
motSkel(l(X))-->l,motSkel(X).
motSkel(a(X,Y))-->a,motSkel(X),motSkel(Y).

isClosable(X):-isClosable(X,0).
  
isClosable(v,V):-V>0.
isClosable(l(A),V):-succ(V,NewV),isClosable(A,NewV).  
isClosable(a(A,B),V):-
  isClosable(A,V),
  isClosable(B,V).

closableSkel(N,X):-motSkel(N,X),isClosable(X).

unClosableSkel(N,X):-motSkel(N,X),not(isClosable(X)).

quickClosableSkel(N,X):-quickClosableSkel(X,0,N,0).

quickClosableSkel(v,V)-->{V>0}.
quickClosableSkel(l(A),V)-->l,{succ(V,NewV)},quickClosableSkel(A,NewV).  
quickClosableSkel(a(A,B),V)-->a,
  quickClosableSkel(A,V),
  quickClosableSkel(B,V).

closable(N,X):-closable(X,N,0).

closable(l(Z))-->l,motSkel(Z).
closable(a(X,Y))-->a,closable(X),closable(Y).

uniquelyClosable1(N,X):-uniquelyClosable1(X,0,N,0).

uniquelyClosable1(v,1)-->[].
uniquelyClosable1(l(A),V)-->l,{succ(V,NewV)},uniquelyClosable1(A,NewV).  
uniquelyClosable1(a(A,B),V)-->a,uniquelyClosable1(A,V),
  uniquelyClosable1(B,V).

uniquelyClosable2(N,X):-uniquelyClosable2(X,hasNoLambda,N,0).

uniquelyClosable2(v,hasOneLambda)-->[].
uniquelyClosable2(l(A),hasNoLambda)-->l,
  uniquelyClosable2(A,hasOneLambda).
uniquelyClosable2(a(A,B),Has)-->a,uniquelyClosable2(A,Has),
  uniquelyClosable2(B,Has).

uniquelyClosable(N,X):-uniquelyClosable(X,N,0).

uniquelyClosable(l(A))-->l,closedAbove(A).
uniquelyClosable(a(A,B))-->a,uniquelyClosable(A),uniquelyClosable(B).

closedAbove(v)-->[].
closedAbove(a(A,B))-->a,closedAbove(A),closedAbove(B).

uniquelyClosableCount(N):-uniquelyClosableCount(N,0).

uniquelyClosableCount-->l,closedAboveCount.
uniquelyClosableCount-->a,uniquelyClosableCount,uniquelyClosableCount.

closedAboveCount-->[].
closedAboveCount-->a,closedAboveCount,closedAboveCount.

genSkelEqs(N,X,T,Eqs):-genSkelEqs(X,T,[],Eqs,true,N,0).

genSkelEqs(v,V,Vs,(el(V,Vs),Es),Es)-->{Vs=[_|_]}.
genSkelEqs(l(A),(S->T),Vs,Es1,Es2)-->l,genSkelEqs(A,T,[S|Vs],Es1,Es2).  
genSkelEqs(a(A,B),T,Vs,Es1,Es3)-->a,genSkelEqs(A,(S->T),Vs,Es1,Es2),
  genSkelEqs(B,S,Vs,Es2,Es3).

el(V,Vs):-member(V0,Vs),unify_with_occurs_check(V0,V).

typableClosedTerm(N,Term):-genSkelEqs(N,Term,_,Eqs),Eqs.

typableSkel(N,Skel):-genSkelEqs(N,Skel,_,Eqs),once(Eqs).
untypableSkel(N,Skel):-genSkelEqs(N,Skel,_,Eqs),not(Eqs).

uniquelyTypableSkel(N,Skel):-
  genSkelEqs(N,Skel,_,Eqs),has_unique_answer(Eqs).

has_unique_answer(G):-findnsols(2,G,G,Sols),!,Sols=[G].

uniquelyClosableTypable(N,X):-
  uniquelyClosable(N,X),isUniquelyTypableSkel(X).

isUniquelyTypableSkel(X):-skelType(X,_).

skelType(X,T):-skelType(X,T,[]).

skelType(v,V,[V0]):-unify_with_occurs_check(V,V0).
skelType(l(A),(S->T),Vs):-skelType(A,T,[S|Vs]). 
skelType(a(A,B),T,Vs):-skelType(A,(S->T),Vs),skelType(B,S,Vs).

% generate uniformly random closable skeleton X
% of size between MinN and MaxN
genRanCL(MinN,MaxN):- 
  time(genRanCL(100000,MinN,MaxN,R,I)),
  writeln(R), % comment out for large sizes
  writeln(I),
  fail
; true.

% restart until a convenient term is generated
genRanCL(Tries,MinN,MaxN,X,I):-
  between(1,Tries,I),
  tryRanCL(MinN,MaxN,X),
  !.

% try to generate a term of size from MinN to MaxN
tryRanCL(MinN,MaxN,X):-
  random(R),
  ranCL(R,MaxN,X,MaxN,Dif),
  MaxN-Dif>=MinN.

% ensure random value R is below threshold
below(R,P,MaxN,N,N):-R=<P,N<MaxN.

% follow the grammar steps with given Boltzmann probabilities
% and pick lambda node with Motzkin trees below it 
% or subtrees with lambdas above them  
ranCL(R,MaxN,l(Z))-->below(R,0.8730398709632761,MaxN),!,
  l,
  {random(R1)},
  ranMot(R1,MaxN,Z).
ranCL(_,MaxN,a(X,Y))-->a,
  {random(R1),random(R2)},
  ranCL(R1,MaxN,X),
  ranCL(R2,MaxN,Y).

% generate Random Motzkin tree
ranMot(R,MaxN,v)-->below(R,0.3341408333975344,MaxN),!.
ranMot(R,MaxN,l(Z))-->below(R,0.667473848839429,MaxN),!,
  l,
  {random(R1)},
  ranMot(R1,MaxN,Z).
ranMot(_,MaxN,a(X,Y))-->a,
  {random(R1),random(R2)},
  ranMot(R1,MaxN,X),
  ranMot(R2,MaxN,Y).

% generate uniformly random uniquely closable skeleton X
% of size between MinN and MaxN
genRanUC(MinN,MaxN):- 
  time(genRanUC(100000,MinN,MaxN,R,I)),
  writeln(R), % to be commented out if too big
  writeln(tries=I),
  fail
; 
  true.

% restart until a convenient term is generated
genRanUC(Tries,MinN,MaxN,X,I):-
  between(1,Tries,I),
  tryRanUC(MinN,MaxN,X),
  !.

% try to generate a uniquely closable term 
% of size from MinN to MaxN
tryRanUC(MinN,MaxN,X):-
  random(R),
  ranUC(R,MaxN,X,MaxN,Dif),
  MaxN-Dif>=MinN.

% follow the grammar steps with given Boltzmann probabilities
% and pick unique lambda node or subtrees with lambdas in them
ranUC(R,MaxN,l(A))-->below(R,0.5001253328728457,MaxN),!,
  l,
  {random(R1)},
  ranCA(R1,MaxN,A).
ranUC(_,MaxN,a(A,B))-->a,
  {random(R1),random(R2)},
  ranUC(R1,MaxN,A),
  ranUC(R2,MaxN,B).

% generate binary subtree with no lambda in it
ranCA(R,MaxN,v)-->below(R,0.5001253328728457,MaxN),!.
ranCA(_,MaxN,a(A,B))-->
  a,
  {random(R1),random(R2)},
  ranCA(R1,MaxN,A),
  ranCA(R2,MaxN,B).
  
sampler_test1:-
  genRanCL(100000,200000).

sampler_test2:-
  genRanUC(100000,200000).


% Motzkin numbers: [1,1,2,4,9,21,51,127,323,835,2188,5798,15511,41835]
cm(N):-ncounts(N,motSkel(_,_)). 
bm(N):-ntimes(N,motSkel(_,_)).
sm(N):-nshow(N,motSkel(_,_)). 
pm(N):-npp(N,motSkel(_,_)). 
qm(N):-qpp(N,motSkel(_,_)).

% A135501 [0, 1,2,4,13,42,139,506,1915,7558,31092]
cc(N):-ncounts(N,closedTerm(_,_)). 
bc(N):-ntimes(N,closedTerm(_,_)).
sc(N):-nshow(N,closedTerm(_,_)). 
pc(N):-npp(N,closedTerm(_,_)). 
qc(N):-qpp(N,closedTerm(_,_)).

% [0,1,1,2,5,11,26,65,163,417,1086]
ccs(N):-ncounts(N,closableSkel(_,_)). 
bcs(N):-ntimes(N,closableSkel(_,_)).
scs(N):-nshow(N,closableSkel(_,_)). 
pcs(N):-npp(N,closableSkel(_,_)). 
qcs(N):-qpp(N,closableSkel(_,_)).

% [0,1,1,2,5,11,26,65,163,417,1086]
ccs1(N):-ncounts(N,closable(_,_)). 
bcs1(N):-ntimes(N,closable(_,_)).
scs1(N):-nshow(N,closable(_,_)). 
pcs1(N):-npp(N,closable(_,_)). 
qcs1(N):-qpp(N,closable(_,_)).

% [0,1,1,2,5,11,26,65,163,417,1086]
cncs(N):-ncounts(N,unClosableSkel(_,_)). 
bncs(N):-ntimes(N,unClosableSkel(_,_)).
sncs(N):-nshow(N,unClosableSkel(_,_)). 
pncs(N):-npp(N,unClosableSkel(_,_)). 
qncs(N):-qpp(N,unClosableSkel(_,_)).

% [0,1,1,2,5,11,26,65,163,417,1086]
cqs(N):-ncounts(N,quickClosableSkel(_,_)). 
bqs(N):-ntimes(N,quickClosableSkel(_,_)).
sqs(N):-nshow(N,quickClosableSkel(_,_)). 
pqs(N):-npp(N,quickClosableSkel(_,_)). 
qqs(N):-qpp(N,quickClosableSkel(_,_)).


buc1(N):-ntimes(N,uniquelyClosable1(_,_)).
buc2(N):-ntimes(N,uniquelyClosable1(_,_)).

% uniquely closable, very fast 
% 0,1,0,1,1,2,2,7,5,20,19,60,62,202,202,679,711,2304,2507,8046,8856
cuc(N):-ncounts(N,uniquelyClosable(_,_)). 
buc(N):-ntimes(N,uniquelyClosable(_,_)).
suc(N):-nshow(N,uniquelyClosable(_,_)). 
puc(N):-npp(N,uniquelyClosable(_,_)). 
quc(N):-qpp(N,uniquelyClosable(_,_)).

% 0,1,2,3,10,34,98,339,1263,4626,18099,73782,306295,1319660,5844714,26481404,123172740
ct(N):-ncounts(N,typableClosedTerm(_,_)). 
bt(N):-ntimes(N,typableClosedTerm(_,_)).
st(N):-nshow(N,typableClosedTerm(_,_)). 
pt(N):-npp(N,typableClosedTerm(_,_)). 
qt(N):-qpp(N,typableClosedTerm(_,_)). 

% 0,1,1,1,5,9,17,55,122,289,828,2037,5239,14578,37942
cts(N):-ncounts(N,typableSkel(_,_)). 
bts(N):-ntimes(N,typableSkel(_,_)).
sts(N):-nshow(N,typableSkel(_,_)). 
pts(N):-npp(N,typableSkel(_,_)). 
qts(N):-qpp(N,typableSkel(_,_)). 

% [0,0,0,1,0,2,9,10,41,128,258,821,2360,5813,17185,48721,129678]
cuts(N):-ncounts(N,untypableSkel(_,_)).
buts(N):-ntimes(N,untypableSkel(_,_)).
suts(N):-nshow(N,untypableSkel(_,_)).  
puts(N):-npp(N,untypableSkel(_,_)).
quts(N):-qpp(N,untypableSkel(_,_)).


% 0,1,0,0,2,0,1,7,1,13,34,20,100,226,234,853,1877,2650,8128,18116,30483,85713
cus(N):-ncounts(N,uniquelyTypableSkel(_,_)). 
bus(N):-ntimes(N,uniquelyTypableSkel(_,_)).
sus(N):-nshow(N,uniquelyTypableSkel(_,_)). 
pus(N):-npp(N,uniquelyTypableSkel(_,_)). 
qus(N):-qpp(N,uniquelyTypableSkel(_,_)).

% uniquely closable uniquely typable
% 0,1,0,0,1,0,0,2,0,0,5,0,0,14,0,0,42,0,0,132 - Catalan
cucut(N):-ncounts(N,uniquelyClosableTypable(_,_)). 
bucut(N):-ntimes(N,uniquelyClosableTypable(_,_)).
sucut(N):-nshow(N,uniquelyClosableTypable(_,_)). 
pucut(N):-npp(N,uniquelyClosableTypable(_,_)). 
qucut(N):-qpp(N,uniquelyClosableTypable(_,_)).

go:-N=13,
  Tests=[cm,cc,ccs,cncs,cqs,cuc,ct,cts,cuts,cus,cucut],
  forall(member(F,Tests),call(F,N)).



fig1c:-fig1c(18).
fig1c(N):-time(ncvs2(N,quickClosableSkel(_,_),unClosableSkel(_,_))). 

fig2c:-fig2c(28).
fig2c(N):-time(ncvs(N,uniquelyClosable(_,_))).


fig1t:-fig1t(16).
fig1t(N):-time(ncvs2(N,typableSkel(_,_),untypableSkel(_,_))). 

fig2t:-fig2t(16).
fig2t(N):-time(ncvs(N,uniquelyTypableSkel(_,_))).

figct:-figct(16).
figct(N):-time(ncvs2(N,closableSkel(_,_),typableSkel(_,_))). 


  

