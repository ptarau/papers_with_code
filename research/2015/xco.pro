% PPDP'15
:-use_module(library(lists)).

sT(x>(x>x)).
kT((x>x)>x).
xxT(x>x).

genTree(x)-->[].
genTree(X>Y)-->down,genTree(X),genTree(Y).

down(From,To):-From>0,To is From-1.   

genTree(N,X):-genTree(X,N,0).

genTrees(N,X):-genTree(X,N,_).

tsize(x,0).
tsize((X>Y),S):-tsize(X,A),tsize(Y,B),S is 1+A+B.

eval((F>G),R):-!,eval(F,F1),eval(G,G1),app(F1,G1,R).
eval(X,X).

app((((x>x)>x)>X),_Y,R):-!,R=X. % K
app((((x>(x>x))>X)>Y),Z,R):-!,  % S
  app(X,Z,R1),
  app(Y,Z,R2),
  app(R1,R2,R).
%app((((x>x)>_X)>Y),_Z,R):-!,R=Y. 
%app((x>x)>x,(x>x)>x,R):-!,app(x,x,R).
app(F,G,(F>G)).

kB(l(l(v(1)))).

sB(l(l(l(a(a(v(2),v(0)),a(v(1),v(0))))))).

xB(X):-F=v(0),kB(K),sB(S),X=l(a(a(a(F,K),S),K)).

t2b(x,X):-xB(X).
t2b((X>Y),a(A,B)):-t2b(X,A),t2b(Y,B).

bsize(v(_),0).
bsize(l(A),R):-bsize(A,RA),R is RA+1.
bsize(a(A,B),R):-bsize(A,RA),bsize(B,RB),R is 1+RA+RB.

isClosedB(T):-isClosed1(T,0).

isClosed1(v(N),D):-N<D.
isClosed1(l(A),D):-D1 is D+1,isClosed1(A,D1).
isClosed1(a(X,Y),D):-isClosed1(X,D),isClosed1(Y,D).

btype(v(I),V,Vs):-nth0(I,Vs,V0),
  unify_with_occurs_check(V,V0).
btype(a(A,B),Y,Vs):-btype(A,X>Y,Vs),btype(B,X,Vs).
btype(l(A),X>Y,Vs):-btype(A,Y,[X|Vs]).

btype(A,T):-btype(A,T,[]),bindType(T).

bindType(x):-!.
bindType((A>B)):-bindType(A),bindType(B).

xtype(X,T):-t2b(X,B),btype(B,T).

xt(X,T):-poly_xt(X,T),bindType(T).

xT(T):-t2b(x,B),btype(B,T,[]).

poly_xt(x,T):-xT(T).
poly_xt(A>B,Y):-poly_xt(A,T),poly_xt(B,X),
  unify_with_occurs_check(T,(X>Y)).

cat(0,1).
cat(N,R):-
  N>0, PN is N-1, SN is N+1,
  cat(PN,R1),
  R is 2*(2*N-1)*R1//SN.

genTyped(L,X,T):-
  genTree(L,X),
  xtype(X,T).
  
countTyped(L,Typed,Cats,Prop):-
  sols(genTyped(L,_,_),Typed),
  cat(L,Cats),
  Prop is Typed/Cats.
  
tcounts:-
  between(0,12,I),countTyped(I,Typed,All,Prop),
  write((I,&,Typed,&,All,&,Prop)),nl,fail.

genTypedB(v(I),V,Vs)--> {
   nth0(I,Vs,V0),
   unify_with_occurs_check(V,V0)
  }.
genTypedB(a(A,B),Y,Vs)-->down,
  genTypedB(A,X>Y,Vs),
  genTypedB(B,X,Vs).
genTypedB(l(A),X>Y,Vs)-->down,
  genTypedB(A,Y,[X|Vs]). 

genTypedB(L,B,T):-genTypedB(B,T,[],L,0),bindType(T).

genTypedBs(L,B,T):-genTypedB(B,T,[],L,_),bindType(T).

genTypedWithSomeFree(Size,NbFree,B,T):-
   between(0,NbFree,NbVs),
   length(FreeVs,NbVs),
   genTypedB(B,T,FreeVs,Size,0),
   bindType(T).

countForType(GivenType,M,Rs):-
  findall(R,
    (
       between(1,M,L),sols(genTypedB(L,_B,GivenType),R)
    ),
  Rs).   
   
countWithFree(M,K,Rs):-
  findall(R,
    (
       between(1,M,L),sols(genTypedWithSomeFree(L,K,_B,_T),R)
    ),
  Rs).   

genByTypeB(L,B,T):-
  genTree(L,T),
  genTypedBs(L,B,T).

countByTypeB(M,Rs):-
  findall(R,
    (
       between(1,M,L),sols(genByTypeB(L,_B,_T),R)
    ),
  Rs).

iterType(K,X, Ts, Steps):-
  iterType(K,FinalK,X,[],Rs),
  reverse(Rs,Ts),
  Steps is K-FinalK.

iterType(K,FinalK,X,Xs,Ys):-K>0,K1 is K-1,
  xtype(X,T),
  \+(member(T,Xs)),
  !,
  iterType(K1,FinalK,T,[T|Xs],Ys).
iterType(FinalK,FinalK,_,Xs,Xs).


itersFrom(T,Size,Steps,Avg):-
  tsize(T,Size),
  iterType(100,T,Ts0,Steps),
  Ts=[T|Ts0],
  maplist(tsize,Ts,Sizes),
  avg(Sizes,Avg).

avg(Ns,Avg):-
  length(Ns,Len),
  sumlist(Ns,Sum),
  Avg is Sum/Len.

iterLens(M):-
  between(0,M,I),
  findall([Steps,AvgSize],(genTree(I,T),itersFrom(T,_Size,Steps,AvgSize)),Rs),
  % write(rs=Rs),nl,
  length(Rs,Len),
  foldl(msum,Rs,[0,0],Sums),
  maplist(divWith(Len),Sums,Avgs),
  write(avgs=[I|Avgs]),nl,
  fail.
  
msum([A,B],[D,E],[X,Y]):-
  X is A+D,Y is B+E.

  
msum([A,B,C],[D,E,F],[X,Y,Z]):-
  X is A+D,Y is B+E,Z is C+F.

divWith(X,Y,R):-R is Y / X.
    

iterTo(M):-
  between(0,M,I),
  t(I,T),tsize(T,Size),
  iterType(100,T,Ts,Steps),
  maplist(tsize,Ts,Sizes),
  length(Sizes,Len),
  sumlist(Sizes,Sum),
  Avg is Sum / Len,
  write((I,Steps,Size,Avg)),
  nl,
  fail.

beta(l(A),B,R):-subst(A,0,B,R).

subst(a(A1,A2),I,B,a(R1,R2)):-I>=0,
  subst(A1,I,B,R1),
  subst(A2,I,B,R2).   
subst(l(A),I,B,l(R)):-I>=0,I1 is I+1,
  subst(A,I1,B,R).
subst(v(N),I,_B,v(N1)):-I>=0,N>I,N1 is N-1. 
subst(v(N),I,_B,v(N)):-I>=0,N<I.
subst(v(N),I,B,R):-I>=0,N=:=I,
  shift_var(I,0,B,R).

shift_var(I,K,a(A,B),a(RA,RB)):-K>=0,I>=0,
  shift_var(I,K,A,RA),
  shift_var(I,K,B,RB).
shift_var(I,K,l(A),l(R)):-K>=0,I>=0,K1 is K+1,
  shift_var(I,K1,A,R).
shift_var(I,K,v(N),v(M)):-K>=0,I>=0,N>=K,M is N+I.
shift_var(I,K,v(N),v(N)):-K>=0,I>=0,N<K.

wh_nf(v(X),v(X)).
wh_nf(l(E),l(E)).
wh_nf(a(X,Y),Z):-wh_nf(X,X1),wh_nf1(X1,Y,Z).

wh_nf1(v(X),Y,a(v(X),Y)).
wh_nf1(l(E),Y,Z):-beta(l(E),Y,NewE),wh_nf(NewE,Z).
wh_nf1(a(X1,X2),Y,a(a(X1,X2),Y)).

evalB(v(X),v(X)).
evalB(l(E),l(NE)):-evalB(E,NE).
evalB(a(E1,E2),R):-wh_nf(E1,NE),applyB(NE,E2,R).

applyB(v(E1),E2,a(v(E1),NE2)):-evalB(E2,NE2).
applyB(l(E),E2,R):-beta(l(E),E2,NewE),evalB(NewE,R).
applyB(a(A,B),E2,a(NE1,NE2)):-
  evalB(a(A,B),NE1),
  evalB(E2,NE2).

evalAsT --> eval,t2b.
evalAsB --> t2b,evalB.

cons(I,J,C) :- I>=0,J>=0,
  D is mod(J+1,2),
  C is 2^(I+1)*(J+D)-D.

decons(K,I1,J1):-K>0,B is mod(K,2),KB is K+B,
  dyadicVal(KB,I,J),
  I1 is max(0,I-1),J1 is J-B.

dyadicVal(KB,I,J):-I is lsb(KB),J is KB // (2^I).

n(x,0).
n((A>B),K):-n(A,I),n(B,J),cons(I,J,K).

t(0,x).
t(K,(A>B)):-K>0,decons(K,I,J),t(I,A),t(J,B).

parity(x,0).
parity(_>x,1).
parity(_>(X>Xs),P1):-parity(X>Xs,P0),P1 is 1-P0.

even_(_>Xs):-parity(Xs,1).
odd_(_>Xs):-parity(Xs,0).

s(x,x>x).
s(X>x,X>(x>x)):-!.
s(X>Xs,Z):-parity(X>Xs,P),s1(P,X,Xs,Z).

s1(0,x,X>Xs,SX>Xs):-s(X,SX).
s1(0,X>Ys,Xs,x>(PX>Xs)):-p(X>Ys,PX).
s1(1,X,x>(Y>Xs),X>(SY>Xs)):-s(Y,SY).
s1(1,X,Y>Xs,X>(x>(PY>Xs))):-p(Y,PY).

p(x>x,x).
p(X>(x>x),X>x):-!.
p(X>Xs,Z):-parity(X>Xs,P),p1(P,X,Xs,Z).

p1(0,X,x>(Y>Xs),X>(SY>Xs)):-s(Y,SY).
p1(0,X,(Y>Ys)>Xs,X>(x>(PY>Xs))):-p(Y>Ys,PY).
p1(1,x,X>Xs,SX>Xs):-s(X,SX).
p1(1,X>Ys,Xs, x>(PX>Xs)):-p(X>Ys,PX).

borrow(Op,X,Y,R):-n(X,A),n(Y,B),
  ArithOp=..[Op,A,B],C is ArithOp,t(C,R).
  
add(X,Y,R):-borrow(+,X,Y,R).
sub(X,Y,R):-borrow(-,X,Y,R).

rank(v(0),x).
rank(l(A),x>T):-rank(A,T).
rank(v(K),T>x):-K>0,t(K,T).
rank(a(A,B),X1>Y1):-rank(A,X),s(X,X1),rank(B,Y),s(Y,Y1).

unrank(x,v(0)).
unrank(x>T,l(A)):-!,unrank(T,A).
unrank(T>x,v(N)):-!,n(T,N).
unrank(X>Y,a(A,B)):-
  p(X,X1),unrank(X1,A),
  p(Y,Y1),unrank(Y1,B).

genSelfTypedT(L,T):-genTree(L,T),xtype(T,T).

countSelfTypedT(M,Rs):-
  findall(R,
    (
       between(1,M,L),sols(genSelfTypedT(L,_T),R)
    ),
  Rs).  

b2b --> rank,t2b.
t2t --> t2b,rank.

evalOrNextB(B,EvB):-btype(B,_),evalB(B,EvB),EvB\==B,!.
evalOrNextB(B,NextB):-
  rank(B,T),
  s(T,NextT),
  unrank(NextT,NextB).

playWithB(Term,Steps,Orbit):-
  playWithB(Term,Steps,Orbit,[]).

playWithB(Term,Steps,[NewTerm|Ts1],Ts2):-Steps>0,!,
  Steps1 is Steps-1,
  evalOrNextB(Term,NewTerm),
  playWithB(NewTerm,Steps1,Ts1,Ts2).
playWithB(Term,_,[Term|Ts],Ts).

evalOrNextT(T,EvT):-xtype(T,_),eval(T,EvT),EvT\==T,!.
evalOrNextT(T,NextT):-s(T,NextT).

playWithT(Term,Steps,Orbit):-playWithT(Term,Steps,Orbit,[]).

playWithT(Term,Steps,[NewTerm|Ts1],Ts2):-Steps>0,!,
  Steps1 is Steps-1,
  evalOrNextT(Term,NewTerm),
  playWithT(NewTerm,Steps1,Ts1,Ts2).
playWithT(Term,_,[Term|Ts],Ts).

t2p(T,Ps):-t2p(T,0,1,Ps,[]).

t2p(X,L,R) --> [L],t2ps(X,L,R).

t2ps(x,_,R) --> [R].
t2ps((X>Xs),L,R) --> t2p(X,L,R),t2ps(Xs,L,R). 

% generators
ttsizes:-
 between(0,1000,N),t(N,T),t2t(T,TT),tsize(T,S1),
 tsize(TT,S2),write((N,S1,S2)),nl,fail.
 
nonetyped:-
  between(0,10000,N),t(N,T),t2t(T,TT),xtype(TT,_),
  write(N),nl,fail.
 
ctest(M):-
  closedTo(M,I,B),
  write(I),write(' '),lb(B),
  fail.

closedTo(M,I,B):-
  between(0,M,I),
  t(I,T),
  unrank(T,B),
  isClosedB(B).

typedTo(M,I,B,T):-
  between(0,M,I),
  t(I,T),
  unrank(T,B),
  isClosedB(B),
  btype(B,T).
 
ttyped(From,To,I,TT):-between(From,To,I),t(I,T),t2b(T,B),btype(B,TT). 

bclosed(From,To,I):-between(From,To,I),t(I,T),unrank(T,B),isClosedB(B).

% counts

ccount(M,R):-sols(closedTo(M,_,_),R).

tcount(M,R):-sols(typedTo(M,_,_,_),R). 

tcount1(M,R):-sols(ttyped(M,_I,_TT),R). 
  
% 22527 first non-stopping evalB
    

% tests

skxT((S>K)>x):-sT(S),kT(K).

skkT((S>K)>K):-sT(S),kT(K).

siiT(R) :- sT(S),skkT(I),R=((S>I)>I).

omegaT(SII>SII):-siiT(SII).

iB(l(v(0))).

skkB(I):-sB(S),kB(K),I=a(a(S,K),K).

siiB(R) :- sB(S),skkB(I),R=a(a(S,I),I).

omegaB(a(SII,SII)):-siiB(SII).

yB(l(a(l(a(v(1),a(v(0),v(0)))),l(a(v(1),a(v(0),v(0))))))).
xfree((x>x)>x,R):-!,R=k.
xfree(x>(x>x),R):-!,R=s.
xfree(X>Y,A>B):-!,xfree(X,A),xfree(Y,B).

o2ks((x>x)>x,R):-!,R=k.
o2ks(x>(x>x),R):-!,R=s.
o2ks(x>x,R):-!,R=xx.
o2ks(X>Y,A>B):-!,o2ks(X,A),o2ks(Y,B).
o2ks(x,x).

ks2o(k,R):-R=((x>x)>x).
ks2o(s,R):-!,R=(x>(x>x)).
ks2o(xx,R):-!,R=(x>x).
ks2o(X>Y,A>B):-!,ks2o(X,A),ks2o(Y,B).
ks2o(x,x).

% helpers

pn(X):-numbervars(X,0,_),write(X),nl.

lb(B):-b2l(B,T),lamshow(T),nl. 
tb(B):-b2l(B,T),texshow(T),nl. 

lx(X):-t2b(X,B),b2l(B,T),lamshow(T),nl. 
tx(X):-t2b(X,B),b2l(B,T),texshow(T),nl. 

% helpers
 
lamshow(T):-
  numbervars(T,0,_),
  lamshow(T,Cs,[]),
  maplist(write,Cs),
  fail.
lamshow(_).

b2l(A,T):-b2l(A,T,_Vs).

b2l(v(I),V,Vs):-nth0(I,Vs,V).
b2l(a(A,B),a(X,Y),Vs):-b2l(A,X,Vs),b2l(B,Y,Vs).
b2l(l(A),l(V,Y),Vs):-b2l(A,Y,[V|Vs]).


lamshow('$VAR'(I))--> [x],[I].
lamshow(l('$VAR'(I),E))-->[('(')],[('\\')],[x],[I],[('.')],lamshow(E),[(')')].
lamshow(a(X,Y))-->[('(')],lamshow(X),[(' ')],lamshow(Y),[(')')].

texshow(T):-
  numbervars(T,0,_),
  texshow(T,Cs,[]),
  maplist(write,Cs),
  fail.
texshow(_).

texshow('$VAR'(I))--> [x],[I].
texshow(l('$VAR'(I),E))-->[(' ')],[('~\\lambda ')],[x],[I],[('.')],texshow(E),[(' ')].
texshow(a(X,Y))-->[('(')],texshow(X),[('~')],texshow(Y),[(')')].

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


