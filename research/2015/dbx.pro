% PADL'15

b2l(A,T):-b2l(A,T,_Vs).

b2l(v(I),V,Vs):-nth0(I,Vs,V).
b2l(a(A,B),a(X,Y),Vs):-b2l(A,X,Vs),b2l(B,Y,Vs).
b2l(l(A),l(V,Y),Vs):-b2l(A,Y,[V|Vs]).

l2b(A,T):-copy_term(A,CA),numbervars(CA,0,_),l2b(CA,T,_Vs).

l2b('$VAR'(V),v(I),Vs):-once(nth0(I,Vs,'$VAR'(V))).
l2b(a(X,Y),a(A,B),Vs):-l2b(X,A,Vs),l2b(Y,B,Vs).
l2b(l(V,Y),l(A),Vs):-l2b(Y,A,[V|Vs]).

b2c(v(X),v(0,X)). 
b2c(a(X,Y),a(0,A,B)):-b2c(X,A),b2c(Y,B). 
b2c(l(X),R):-b2c1(0,X,R).

b2c1(K,a(X,Y),a(K1,A,B)):-up(K,K1),b2c(X,A),b2c(Y,B).
b2c1(K, v(X),v(K1,X)):-up(K,K1).
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

dcat(_,o).
dcat(D1,(X->Y)):-down(D1,D2),dcat(D2,X),dcat(D2,Y).

scat(N,T):-scat(T,N,0).
 
scat(o)-->[].
scat((X->Y))-->down,scat(X),scat(Y).

extractType(_:TX,TX):-!. % this matches all variables
extractType(l(_:TX,A),(TX->TA)):-extractType(A,TA).
extractType(a(A,B),TY):-extractType(A,(TX->TY)),extractType(B,TX).

hasType(CTerm,Type):-
  c2l(CTerm,LTerm),
  extractType(LTerm,Type),
  acyclic_term(LTerm),
  bindType(Type).

bindType(o):-!.
bindType((A->B)):-bindType(A),bindType(B).  

typeable(Term):-hasType(Term,_Type).

motzkinTree(L,T):-motzkinTree(T,L,0).

motzkinTree(u)-->down.
motzkinTree(l(A))-->down,motzkinTree(A).
motzkinTree(a(A,B))-->down,motzkinTree(A),motzkinTree(B).

genDB(v(X),V)-->{down(V,V0),between(0,V0,X)}.
genDB(l(A),V)-->down,{up(V,NewV)},genDB(A,NewV).
genDB(a(A,B),V)-->down,genDB(A,V),genDB(B,V).  

genDB(L,T):-genDB(T,0,L,0).
genDBs(L,T):-genDB(T,0,L,_).

genCompressed --> genDB,b2c.
genCompresseds--> genDBs,b2c.

genStandard-->genDB,b2l.
genStandards-->genDBs,b2l.

genLambda(L,T):-genLambda(T,[],L,0).

genLambda(X,Vs)-->{member(X,Vs)}.
genLambda(l(X,A),Vs)-->down,genLambda(A,[X|Vs]).
genLambda(a(A,B),Vs)-->down,genLambda(A,Vs),genLambda(B,Vs).

genTypeable(L,T):-genCompressed(L,T),typeable(T).
genTypeables(L,T):-genCompresseds(L,T),typeable(T).

nf(v(X),V)-->{down(V,V0),between(0,V0,X)}.
nf(l(A),V)-->down,{up(V,NewV)},nf(A,NewV).
nf(a(v(X),B),V)-->down,nf(v(X),V),nf(B,V).  
nf(a(a(X,Y),B),V)-->down,nf(a(X,Y),V),nf(B,V).  

nf(L,T):-nf(B,0,L,0),b2c(B,T).
nfs(L,T):-nf(B,0,L,_),b2c(B,T).

linLamb(X,[X])-->[].
linLamb(l(X,A),Vs)-->down,linLamb(A,[X|Vs]).
linLamb(a(A,B),Vs)-->down,
  {subset_and_complement_of(Vs,As,Bs)},
  linLamb(A,As),linLamb(B,Bs).

subset_and_complement_of([],[],[]).
subset_and_complement_of([X|Xs],NewYs,NewZs):-
  subset_and_complement_of(Xs,Ys,Zs),
  place_element(X,Ys,Zs,NewYs,NewZs).

place_element(X,Ys,Zs,[X|Ys],Zs).
place_element(X,Ys,Zs,Ys,[X|Zs]).

linLamb(L,CT):-linLamb(T,[],L,0),l2c(T,CT).

afLinLamb(L,CT):-afLinLamb(T,[],L,0),l2c(T,CT).

afLinLamb(X,[X|_])-->[].
afLinLamb(l(X,A),Vs)-->down,afLinLamb(A,[X|Vs]).
afLinLamb(a(A,B),Vs)-->down,
  {subset_and_complement_of(Vs,As,Bs)},
  afLinLamb(A,As),afLinLamb(B,Bs).

boundedUnary(v(X),V,_D)-->{down(V,V0),between(0,V0,X)}.
boundedUnary(l(A),V,D1)-->down,
  {down(D1,D2),up(V,NewV)},
  boundedUnary(A,NewV,D2).
boundedUnary(a(A,B),V,D)-->down,
  boundedUnary(A,V,D),boundedUnary(B,V,D).  

boundedUnary(D,L,T):-boundedUnary(B,0,D,L,0),b2c(B,T).
boundedUnarys(D,L,T):-boundedUnary(B,0,D,L,_),b2c(B,T).

blc(L,T):-blc(L,T,_Cs).

blc(L,T,Cs):-length(Cs,L),blc(B,0,Cs,[]),b2c(B,T).

blc(v(X),V)-->{between(1,V,X)},encvar(X).
blc(l(A),V)-->[0,0],{NewV is V+1},blc(A,NewV).
blc(a(A,B),V)-->[0,1],blc(A,V),blc(B,V).  

encvar(0)-->[0].
encvar(N)-->{down(N,N1)},[1],encvar(N1).

beta(l(A),B,R):-subst(A,0,B,R).

subst(a(A1,A2),I,B,a(R1,R2)):-I>=0,
  subst(A1,I,B,R1),
  subst(A2,I,B,R2).   
subst(l(A),I,B,l(R)):-I>=0,I1 is I+1,subst(A,I1,B,R).
subst(v(N),I,_B,v(N1)):-I>=0,N>I,N1 is N-1. 
subst(v(N),I,_B,v(N)):-I>=0,N<I.
subst(v(N),I,B,R):-I>=0,N=:=I,shift_var(I,0,B,R).

shift_var(I,K,a(A,B),a(RA,RB)):-K>=0,I>=0,
  shift_var(I,K,A,RA),
  shift_var(I,K,B,RB).
shift_var(I,K,l(A),l(R)):-K>=0,I>=0,K1 is K+1,shift_var(I,K1,A,R).
shift_var(I,K,v(N),v(M)):-K>=0,I>=0,N>=K,M is N+I.
shift_var(I,K,v(N),v(N)):-K>=0,I>=0,N<K.

wh_nf(v(X),v(X)).
wh_nf(l(E),l(E)).
wh_nf(a(X,Y),Z):-wh_nf(X,X1),wh_nf1(X1,Y,Z).

wh_nf1(v(X),Y,a(v(X),Y)).
wh_nf1(l(E),Y,Z):-beta(l(E),Y,NewE),wh_nf(NewE,Z).
wh_nf1(a(X1,X2),Y,a(a(X1,X2),Y)).

to_nf(v(X),v(X)).
to_nf(l(E),l(NE)):-to_nf(E,NE).
to_nf(a(E1,E2),R):-wh_nf(E1,NE),to_nf1(NE,E2,R).

to_nf1(v(E1),E2,a(v(E1),NE2)):-to_nf(E2,NE2).
to_nf1(l(E),E2,R):-beta(l(E),E2,NewE),to_nf(NewE,R).
to_nf1(a(A,B),E2,a(NE1,NE2)):-to_nf(a(A,B),NE1),to_nf(E2,NE2).

evalStandard-->l2b,to_nf,b2l.
evalCompressed-->c2b,to_nf,b2c.




% tests
    

tgo(L):-
  gen(genDB,L,B),
  tshow(B).
  
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
  ; write('!!! NOT typeable !!!'),
    evalStandard(X,Y)->nl,write('EVAL='),p(Y)
  ; write('!!! NOT NORMALIZED in 100 steps !!!')
  ),
  nl,
  fail.
lshow(_).  

% closed/open ratio

ccount(M,R):-sols(cgen(M,_),K),R is K/M.  
  
tsize(v(K,_),K).
tsize(a(K,X,Y),Size):-tsize(X,A),tsize(Y,B),Size is A+B+K+1.    
    
%%%%%%%% helpers %%%%%%

p(T):- numbervars(T,0,_),write(T),fail;true.

pn(T):-p(T),nl.
 
ln(T):-lamshow(T),nl.

lb(B):-b2l(B,T),ln(T). 

lc(C):-c2l(C,T),ln(T). 
 
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

% Church numerals
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

% integers to Church  numerals in de Bruijn form
i2b(0,X):-zero(X).
i2b(K,R):-K>0,K1 is K-1,
  suc(S),i2b(K1,P),to_nf(a(S,P),R).

% Church  numerals in de Bruijn form to integers
b2i(l(l(v(0))),R):-!,R=0.
b2i(X,R):-
  pre(P),
  to_nf(a(P,X),Y),
  b2i(Y,R1),
  R is R1+1.
  
% Testing the Ackerman function with Church numerals

acktest(R):-
  ack(A),
  suc(S),
  two(T),
  to_nf(a(A,a(S,T)),R).
  
atest(I+R):-add(A),i2b(6,X),to_nf(a(a(A,X),X),R),b2i(R,I).
  
go:- acktest(X),b2i(X,I),lb(X),pn(I).


