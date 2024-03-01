% statistics, visuals, figures, tables etc. rely on some files at
% http://www.cse.unt.edu/~tarau/research/2017/lpgen/
:-include('lpgen/stats.pro').

cat_mot(c(e,e),v).
cat_mot(c(X,e),l(A)):-X=c(_,_),cat_mot(X,A).
cat_mot(c(e,Y),r(B)):-Y=c(_,_),cat_mot(Y,B).
cat_mot(c(X,Y),a(A,B)):-X=c(_,_),Y=c(_,_),
  cat_mot(X,A),
  cat_mot(Y,B).

cat(N,X):-cat(X,N,0).

cat(e,N,N).
cat(c(A,B),SN,N3):-succ(N1,SN),cat(A,N1,N2),cat(B,N2,N3).

sum_to(N,c(L,R,A),c(0,0,0)):-N>=0,
  between(0,N,A2),0=:=A2/\1,A is A2>>1,
  LR is N-A2,
  between(0,LR,L),
  R is LR-L.

lDec(c(SL,R,A),c(L,R,A)):-succ(L,SL). 
rDec(c(L,SR,A),c(L,R,A)):-succ(R,SR). 
aDec(c(L,R,SA),c(L,R,A)):-succ(A,SA). 

afLam(N,T):-sum_to(N,Hi,Lo),
  has_enough_lambdas(Hi),
  afLinLam(T,[],Hi,Lo).

has_enough_lambdas(c(L,_,A)):-succ(A,L).

afLinLam(v(X),[X])-->[].
afLinLam(l(X,A),Vs)-->lDec,afLinLam(A,[X|Vs]).
afLinLam(r(A),Vs)-->rDec,afLinLam(A,Vs). 
afLinLam(a(A,B),Vs)-->aDec,
  {subset_and_complement_of(Vs,As,Bs)},
  afLinLam(A,As),
  afLinLam(B,Bs).
  
subset_and_complement_of([],[],[]).
subset_and_complement_of([X|Xs],NewYs,NewZs):-
  subset_and_complement_of(Xs,Ys,Zs),
  place_element(X,Ys,Zs,NewYs,NewZs).

place_element(X,Ys,Zs,[X|Ys],Zs).
place_element(X,Ys,Zs,Ys,[X|Zs]).  

toMotSkel(v(_),v).
toMotSkel(l(X),l(Y)):-toMotSkel(X,Y).
toMotSkel(l(_,X),l(Y)):-toMotSkel(X,Y).
toMotSkel(r(X),l(Y)):-toMotSkel(X,Y).
toMotSkel(a(X,Y),a(A,B)):-toMotSkel(X,A),toMotSkel(Y,B).

afSkelGen(N,S):-afLam(N,T),toMotSkel(T,S).

linSkelGen(N,S):-linLam(N,T),toMotSkel(T,S).

afSkel(N,T):-distinct(T,afSkelGen(N,T)).

linSkel(N,T):-distinct(T,linSkelGen(N,T)).

linLam(N,T):-N mod 3=:=1,
  sum_to(N,Hi,Lo),has_no_unused(Hi),
  afLinLam(T,[],Hi,Lo).

has_no_unused(c(L,0,A)):-succ(A,L).

kColoredClosed(N,X):-kColoredClosed(X,[],N,0).

kColoredClosed(v(I),Vs)-->{nth0(I,Vs,V),inc_var(V)}.
kColoredClosed(l(K,A),Vs)-->l,
  kColoredClosed(A,[V|Vs]),
  {close_var(V,K)}. 
kColoredClosed(a(A,B),Vs)-->a,
  kColoredClosed(A,Vs),
  kColoredClosed(B,Vs).

l(SX,X):-succ(X,SX).
a-->l,l.

inc_var(X):-var(X),!,X=s(_).
inc_var(s(X)):-inc_var(X).
  
close_var(X,K):-var(X),!,K=0.  
close_var(s(X),SK):-close_var(X,K),l(SK,K).

simplyTypedColored(N,X,T):-simplyTypedColored(X,T,[],N,0).

simplyTypedColored(v(X),T,Vss)-->{
    member(Vs:T0,Vss),
    unify_with_occurs_check(T,T0),
    addToBinder(Vs,X)
  }.
simplyTypedColored(l(Vs,A),S->T,Vss)-->l,
  simplyTypedColored(A,T,[Vs:S|Vss]),
  {closeBinder(Vs)}. 
simplyTypedColored(a(A,B),T,Vss)-->a,
  simplyTypedColored(A,(S->T),Vss),
  simplyTypedColored(B,S,Vss).

addToBinder(Ps,P):-var(Ps),!,Ps=[P|_].
addToBinder([_|Ps],P):-addToBinder(Ps,P).
  
closeBinder(Xs):-append(Xs,[],_),!.

toSkels(v(_),v,v).
toSkels(l(Vs,A),l(K,CS),l(S)):-length(Vs,K),toSkels(A,CS,S).
toSkels(a(A,B),a(CA,CB),a(SA,SB)):-
  toSkels(A,CA,SA),
  toSkels(B,CB,SB).

genTypedSkels(N,CS,S):-genTypedSkels(N,_,_,CS,S).

genTypedSkels(N,X,T,CS,S):-
  simplyTypedColored(N,X,T),
  toSkels(X,CS,S).

typableColSkels(N,CS):-genTypedSkels(N,CS,_).

typableSkels(N,S):-genTypedSkels(N,_,S).

slowTypableColSkel(N,CS):-
  distinct(CS,typableColSkels(N,CS)).

slowTypableSkel(N,S):-
  distinct(S,typableSkels(N,S)).

tsize(X,S):-var(X),!,S=0.
tsize((A->B),S):-tsize(A,SA),tsize(B,SB),S is 1+SA+SB.

genEqs(N,X,T,Eqs):-genEqs(X,T,[],Eqs,true,N,0).

genEqs(v(I),V,[V0|Vs],Es1,Es2)-->{add_eq(Vs,V0,V,I,Es1,Es2)}.
genEqs(l(A),(S->T),Vs,Es1,Es2)-->l,genEqs(A,T,[S|Vs],Es1,Es2).  
genEqs(a(A,B),T,Vs,Es1,Es3)-->a,
  genEqs(A,(S->T),Vs,Es1,Es2),
  genEqs(B,S,Vs,Es2,Es3).

add_eq([],V0,V,0,Es,Es):-unify_with_occurs_check(V0,V).
add_eq([V1|Vs],V0,V,I,(el([V0,V1|Vs],V,0,I),Es),Es).  

el(I,Vs,V):-el(Vs,V,0,I).

el([V0|_],V,N,N):-unify_with_occurs_check(V0,V).
el([_|Vs],V,N1,N3):-succ(N1,N2),el(Vs,V,N2,N3).	

untypableSkel(N,Skel):-genEqs(N,X,_,Eqs),
  not(Eqs),toMotSkel(X,Skel).

typableSkel(N,Skel):-genEqs(N,X,_,Eqs),
  once(Eqs),toMotSkel(X,Skel).

uniquelyTypableSkel(N,Skel):-
  genEqs(N,X,_,Eqs),succeeds_once(Eqs),Eqs,
  toMotSkel(X,Skel).

succeeds_once(G):-findnsols(2,_,G,Sols),!,Sols=[_].

remy_init([e(left,A,_),e(right,A,_)]).

left_or_right(I,J):-choice_of(2,Dice),
  left_or_right(Dice,I,J).

choice_of(N,K):-K is random(N).
% choice_of(N,K):-N>0,N1 is N-1,between(0,N1,K).

left_or_right(0,left,right).
left_or_right(1,right,left).

grow(e(LR,A,B), e(LR,A,C),e(I,C,_),e(J,C,B)):-
  left_or_right(I,J).

remy_step(Es,NewEs,L,NewL):-
  NewL is L+2,choice_of(L,Dice),
  remy_step1(Dice,Es,NewEs).

remy_step1(0,[U|Xs],[X,Y,Z|Xs]):-grow(U, X,Y,Z).
remy_step1(D,[A|Xs],[A|Ys]):-D>0,
  D1 is D-1,
  remy_step1(D1,Xs,Ys).

remy_loop(0,[],N,N).
remy_loop(1,Es,N1,N2):-N2 is N1+2,remy_init(Es).
remy_loop(K,NewEs,N1,N3):-K>1,K1 is K-1,
  remy_loop(K1,Es,N1,N2),
  remy_step(Es,NewEs,N2,N3).

bind_nodes([],e).
bind_nodes([X|Xs],Root):-X=e(_,Root,_),
  maplist(bind_internal,[X|Xs]),
  maplist(bind_leaf,[X|Xs]).

bind_internal(e(left,c(A,_),A)).
bind_internal(e(right,c(_,B),B)).

bind_leaf(e(_,_,Leaf)):-Leaf=e->true;true.

remy_term(K,B):-remy_loop(K,Es,0,_),bind_nodes(Es,B).

mot_gen(N,M):-N>0,remy_term(N,C),cat_mot(C,M).

linChoice(K,Ts,I,T0):-K>0,I is random(K),nth0(I,Ts,T0).

expChoice(K,Ts,I,T):-K>0,N is 2^(K-1),
  R is random(N),N1 is N>>1,
  expChoice1(N1,R,Ts,T,0,I).

expChoice1(N,R,[X|_],Y,I,I):-R>=N,!,Y=X.
expChoice1(N,R,[_|Xs],Y,I1,I3):-N1 is N>>1,succ(I1,I2),
  expChoice1(N1,R,Xs,Y,I2,I3).

decorateTyped(M,X,T):-decorateTyped(M,X,T,0,[]).
   
decorateTyped(v,v(I),T,K,Ts):-
  linChoice(K,Ts,I,T0), % <= any size definition!
  unify_with_occurs_check(T,T0).
decorateTyped(l(X),l(A),(S->T),N,Ts):-succ(N,SN),
  decorateTyped(X,A,T,SN,[S|Ts]).
decorateTyped(r(X),r(A),(_->T),N,Ts):-
  decorateTyped(X,A,T,N,Ts).
decorateTyped(a(X,Y),a(A,B),T,N,Ts):-
  decorateTyped(X,A,(S->T),N,Ts),
  decorateTyped(Y,B,S,N,Ts).

ranTyped(N,MaxI,MaxJ,X,T,I,J):-
  between(1,MaxI,I),
    mot_gen(N,Mot),
    between(1,MaxJ,J),
      decorateTyped(Mot,X,T),
  !.

parTyped(N,MaxI,MaxJ,X,T,I,J):-
  Res=[X,T,I,J],
  prolog_flag(cpu_count,MaxThreads), 
  G=ranTyped(N,MaxI,MaxJ,X,T,I,J),
  length(Goals,MaxThreads),
  maplist(=(G),Goals),
  first_solution(Res,Goals,[on_fail(continue)]).


% bijection between N x N and N+
cons(I,J,C) :- I>=0,J>=0,
  D is mod(J+1,2),
  C is 2^(I+1)*(J+D)-D.

% inverse bijection between N+ and N x N
decons(K,I1,J1):-K>0,B is mod(K,2),KB is K+B,
  dyadicVal(KB,I,J),
  I1 is max(0,I-1),J1 is J-B.

% dyadic valuation of KB and residue
dyadicVal(KB,I,J):-I is lsb(KB),J is KB // (2^I).

% bijection between N and set of binary trees
n(e,0).
n(c(A,B),K):-n(A,I),n(B,J),cons(I,J,K).

% inverse bijection between the set of binary trees and N
t(0,e).
t(K,(c(A,B))):-K>0,decons(K,I,J),t(I,A),t(J,B).

% parity of the natural number associated to a tree
parity(e,0).
parity(c(_,e),1).
parity(c(_,c(X,Xs)),P1):-parity(c(X,Xs),P0),P1 is 1-P0.

% image of even in N+
even_(c(_,Xs)):-parity(Xs,1).

% image of odd in N+
odd_(c(_,Xs)):-parity(Xs,0).

% successor
s(e,c(e,e)).
s(c(X,e),c(X,(c(e,e)))):-!.
s(c(X,Xs),Z):-parity(c(X,Xs),P),s1(P,X,Xs,Z).

s1(0,e,c(X,Xs),c(SX,Xs)):-s(X,SX).
s1(0,c(X,Xs),Xs,c(e,c(PX,Xs))):-p(c(X,Xs),PX).
s1(1,X,c(e,c(Y,Xs)),c(X,c(SY,Xs))):-s(Y,SY).
s1(1,X,c(Y,Xs),c(X,c(e,c(PY,Xs)))):-p(Y,PY).

% predecessor
p(c(e,e),e).
p(c(X,c(e,e)),c(X,e)):-!.
p(c(X,Xs),Z):-parity(c(X,Xs),P),p1(P,X,Xs,Z).

p1(0,X,c(e,c(Y,Xs)),c(X,c(SY,Xs))):-s(Y,SY).
p1(0,X,c(c(Y,Ys),Xs),c(X,c(e,c(PY,Xs)))):-p(c(Y,Ys),PY).
p1(1,e,c(X,Xs),c(SX,Xs)):-s(X,SX).
p1(1,c(X,Ys),Xs, c(e,(c(PX,Xs)))):-p(c(X,Ys),PX).

cat2mot(C,M):-s(C,SuccC),cat_mot(SuccC,M).
mot2cat(M,C):-cat_mot(SuccC,M),p(SuccC,C).

rank(M,N):-mot2cat(M,C),n(C,N).

unrank(N,M):-t(N,C),cat2mot(C,M).

cc(N):-ncounts(N,kColoredClosed(_,_)). % 0,1,2,4,13,42,139,506,1915,7558,31092 -- A135501
bc(N):-ntimes(N,kColoredClosed(_,_)).
sc(N):-nshow(N,kColoredClosed(_,_)).  

% Lescanne: 0, 0, 1, 2, 3, 9, 30, 81, 242, 838, 2799, 9365, 33616, 122937, 449698, 1696724, 655885
ca(N):-ncounts(N,afLam(_,_)). % 0,1,2,3,9,30,81,242,838,2799,9365 - 2 for a/2
ba(N):-ntimes(N,afLam(_,_)).
sa(N):-nshow(N,afLam(_,_)). 
pa(N):-npp(N,afLam(_,_)).
qa(N):-qpp(N,afLam(_,_)).

% Lescanne: 1, 5, 60, 1105, 27120, A062980
cl(N):-ncounts(N,linLam(_,_)). % 0,1,0,0,5,0,0,60,0,0,1105 - 2 for a/2
bl(N):-ntimes(N,linLam(_,_)).
sl(N):-nshow(N,linLam(_,_)). 
pl(N):-npp(N,linLam(_,_)).
ql(N):-qpp(N,linLam(_,_)).

%  0,1,1,1,5,9,14,52,115,219,714,1744,3735,11363 - 2 for a/2
cas(N):-ncounts(N,afSkel(_,_)). 
bas(N):-ntimes(N,afSkel(_,_)).
sas(N):-nshow(N,afSkel(_,_)). 
pas(N):-npp(N,afSkel(_,_)).
qas(N):-qpp(N,afSkel(_,_)).

% A002005 = trim(0) in 0,1,0,0,4,0,0,32,0,0,336,0,0,4096, 0,0,54912 - 2 for a/2
% to check: a(n) = 2^(2*n+1)*(3*n)!!/((n+2)!*n!!)
cls(N):-ncounts(N,linSkel(_,_)). 
bls(N):-ntimes(N,linSkel(_,_)).
sls(N):-nshow(N,linSkel(_,_)). 
pls(N):-npp(N,linSkel(_,_)).
qls(N):-qpp(N,linSkel(_,_)).

showTypeSeen(N,BX:T):-simplyTypedColored(N,X,T),showBinders(X,BX).

showBinders(v(X),X).
showBinders(l(Vs,A),l(L,B)):-L=..[~|Vs],showBinders(A,B).
showBinders(a(A,B),a(C,D)):-showBinders(A,C),showBinders(B,D).

% % 0,1,2,4,13,42,139,506,1915,7558,31092 -- A135501
ct(N):-ncounts(N,simplyTypedColored(_,_,_)). 
bt(N):-ntimes(N,simplyTypedColored(_,_,_)).
st(N):-nshow(N,simplyTypedColored(_,_,_)).  
pt(N):-npp(N,showTypeSeen(_,_)).
qt(N):-qpp(N,showTypeSeen(_,_)).

% 0,1,1,1,5,9,17,55,122,289,828,2037,5239,14578,37942
cts(N):-ncounts(N,typableSkel(_,_)). 
bts(N):-ntimes(N,typableSkel(_,_)).
sts(N):-nshow(N,typableSkel(_,_)). 
pts(N):-npp(N,typableSkel(_,_)). 
qts(N):-qpp(N,typableSkel(_,_)). 

% 0,1,0,0,2,0,1,7,1,13,34,20,100,226,234,853,1877
cus(N):-ncounts(N,uniquelyTypableSkel(_,_)). 
bus(N):-ntimes(N,uniquelyTypableSkel(_,_)).
sus(N):-nshow(N,uniquelyTypableSkel(_,_)). 
pus(N):-npp(N,uniquelyTypableSkel(_,_)). 
qus(N):-qpp(N,uniquelyTypableSkel(_,_)).

cuts(N):-ncounts(N,untypableSkel(_,_)).
% 0,0,0,0,0,0,4,0,12,51,56,275,867,1736,5988,17697,
% 43583,134546,390872,1045248,3102275
buts(N):-ntimes(N,untypableSkel(_,_)).
suts(N):-nshow(N,untypableSkel(_,_)).  
puts(N):-npp(N,untypableSkel(_,_)).
quts(N):-qpp(N,untypableSkel(_,_)).

go:-N=10,
  Tests=[cc,ca,cl,cas,cls,ct,cts,cus,cuts],
  forall(member(F,Tests),call(F,N)).
  

