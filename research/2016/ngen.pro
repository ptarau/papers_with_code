% PADL'17
:-ensure_loaded(library(lists)).

genLambda(s(S),X):-genLambda(X,S,0).

genLambda(X,N1,N2):-nth_elem(X,N1,N2).
genLambda(l(A),s(N1),N2):-genLambda(A,N1,N2).  
genLambda(a(A,B),s(s(N1)),N3):-
  genLambda(A,N1,N2),
  genLambda(B,N2,N3).

nth_elem(0,N,N).
nth_elem(s(X),s(N1),N2):-nth_elem(X,N1,N2).	

genClosed(s(S),X):-genClosed(X,[],S,0).

genClosed(X,Vs,N1,N2):-nth_elem_on(X,Vs,N1,N2).
genClosed(l(A),Vs,s(N1),N2):-genClosed(A,[_|Vs],N1,N2).  
genClosed(a(A,B),Vs,s(s(N1)),N3):-
  genClosed(A,Vs,N1,N2),
  genClosed(B,Vs,N2,N3).

nth_elem_on(0,[_|_],N,N).
nth_elem_on(s(X),[_|Vs],s(N1),N2):-nth_elem_on(X,Vs,N1,N2).

genTypable(X,V,Vs,N1,N2):-genIndex(X,Vs,V,N1,N2).
genTypable(l(A),(X->Xs),Vs,s(N1),N2):-genTypable(A,Xs,[X|Vs],N1,N2).  
genTypable(a(A,B),Xs,Vs,s(s(N1)),N3):-
  genTypable(A,(X->Xs),Vs,N1,N2),
  genTypable(B,X,Vs,N2,N3).

genIndex(0,[V|_],V0,N,N):-unify_with_occurs_check(V0,V).
genIndex(s(X),[_|Vs],V,s(N1),N2):-genIndex(X,Vs,V,N1,N2).	

genPlainTypable(S,X,T):-genTypable(S,_,X,T).

genClosedTypable(S,X,T):-genTypable(S,[],X,T).

genTypable(s(S),Vs,X,T):-genTypable(X,T,Vs,S,0).

min_size(120).
max_size(150).
max_steps(10000000).
boltzmann_index(R):-R<0.35700035696434995.
boltzmann_lambda(R):-R<0.6525813160382378.
boltzmann_leaf(R):-R<0.7044190409261122.

ranTypable(X,T,Size,Steps):-
  max_size(Max),
  min_size(Min),
  max_steps(MaxSteps),
  between(1,MaxSteps,Steps),
    random(R),
    ranTypable(Max,R,X,T,[],0,Size0),
  Size0>=Min,
  !,
  Size is Size0+1.

ranTypable(Max,R,X,V,Vs,N1,N2):-boltzmann_index(R),!,
  random(NewR),
  pickIndex(Max,NewR,X,Vs,V,N1,N2).
ranTypable(Max,R,l(A),(X->Xs),Vs,N1,N3):-boltzmann_lambda(R),!,
  next(Max,NewR,N1,N2),
  ranTypable(Max,NewR,A,Xs,[X|Vs],N2,N3).  
ranTypable(Max,_R,a(A,B),Xs,Vs,N1,N5):-
  next(Max,R1,N1,N2),
  ranTypable(Max,R1,A,(X->Xs),Vs,N2,N3),
  next(Max,R2,N3,N4),
  ranTypable(Max,R2,B,X,Vs,N4,N5).

pickIndex(_,R,0,[V|_],V0,N,N):-boltzmann_leaf(R),!,
  unify_with_occurs_check(V0,V).
pickIndex(Max,_,s(X),[_|Vs],V,N1,N3):-
  next(Max,NewR,N1,N2),
  pickIndex(Max,NewR,X,Vs,V,N2,N3).	

next(Max,R,N1,N2):-N1<Max,N2 is N1+1,random(R).

genNF(s(S),X):-genNF(X,S,0).

genNF(X,N1,N2):-nth_elem(X,N1,N2).
genNF(l(A),s(N1),N2):-genNF(A,N1,N2).  
genNF(a(A,B),s(s(N1)),N3):-notLambda(A),genNF(A,N1,N2),genNF(B,N2,N3).

notLambda(0).
notLambda(s(_)).
notLambda(a(_,_)).

genPlainTypableNF(S,X,T):-genTypableNF(S,_,X,T).

genClosedTypableNF(S,X,T):-genTypableNF(S,[],X,T).

genTypableNF(s(S),Vs,X,T):-genTypableNF(X,T,Vs,S,0).

genTypableNF(X,V,Vs,N1,N2):-genIndex(X,Vs,V,N1,N2).
genTypableNF(l(A),(X->Xs),Vs,s(N1),N2):-genTypableNF(A,Xs,[X|Vs],N1,N2).  
genTypableNF(a(A,B),Xs,Vs,s(s(N1)),N3):-notLambda(A),
  genTypableNF(A,(X->Xs),Vs,N1,N2),
  genTypableNF(B,X,Vs,N2,N3).

boltzmann_nf_lambda(R):-R<0.3333158264186935. % an l/1, otherwise neutral
boltzmann_nf_index(R):-R<0.5062759837493023.  % neutral: index, not a/2
boltzmann_nf_leaf(R):-R<0.6666841735813065.   % neutral: 0, otherwise s/1

ranTypableNF(X,T,Size,Steps):-
  max_nf_size(Max),
  min_nf_size(Min),
  max_nf_steps(MaxSteps),
  between(1,MaxSteps,Steps),
    random(R),
    ranTypableNF(Max,R,X,T,[],0,Size0),
  Size0>=Min,
  !,
  Size is Size0+1.

ranTypableNF(Max,R,l(A),(X->Xs),Vs,N1,N3):-
  boltzmann_nf_lambda(R),!, %lambda
  next(Max,NewR,N1,N2),
  ranTypableNF(Max,NewR,A,Xs,[X|Vs],N2,N3).  

ranTypableNF(Max,R,X,V,Vs,N1,N2):-boltzmann_nf_index(R),!,
  random(NewR),
  pickIndexNF(Max,NewR,X,Vs,V,N1,N2). % an index
ranTypableNF(Max,_R,a(A,B),Xs,Vs,N1,N5):- % an application
  next(Max,R1,N1,N2),
  ranTypableNF(Max,R1,A,(X->Xs),Vs,N2,N3),
  next(Max,R2,N3,N4),
  ranTypableNF(Max,R2,B,X,Vs,N4,N5).

pickIndexNF(_,R,0,[V|_],V0,N,N):-boltzmann_nf_leaf(R),!, % zero
  unify_with_occurs_check(V0,V).
pickIndexNF(Max,_,s(X),[_|Vs],V,N1,N3):- % successor
  next(Max,NewR,N1,N2),
  pickIndexNF(Max,NewR,X,Vs,V,N2,N3).	

% genClosedTypable/genClosedTypableNF

nf([1,1,2,4,4,5.666666666666667,5.428571428571429,8.090909090909092,8.64,10.365384615384615,12.49090909090909,14.780082987551868,17.43016759776536,20.40278917145201,24.10769786772678,28.007454573691568,32.84790899966544,38.13516580149207,44.47758790588122,51.5955629249215,60.040419907606]).

plain([1,1,2,4,4.5,4.4,4.384615384615385,5.703703703703703,5.797297297297297,6.1767676767676765,6.988188976377953,7.62582056892779,8.180624835914939,8.953135439534218,9.781185602417915,10.568048629563572,11.469698136454644,12.457100784898252,13.484006626736333,14.592226055606623,15.800088830182036]).

relrats(Rs):-plain(Ps),nf(Ns),ratios2(Ns,Ps,Rs).

cp(N):-counts(N,genLambda(_,_)). % 0,1,2,4,9,22,57,154,429,1223,3550
bp(N):-times(N,genLambda(_,_)).
sp(N):-show(N,genLambda(_,_)).  

cc(N):-counts(N,genClosed(_,_)). % 0,0,1,1,3,6,17,41,116,313,895
bc(N):-times(N,genClosed(_,_)).
sc(N):-show(N,genClosed(_,_)).  


cpt(N):-counts(N,genPlainTypable(_,_,_)). % 0,1,2,3,8,17,42,106,287,747,2069
bpt(N):-times(N,genPlainTypable(_,_,_)).
spt(N):-show(N,genPlainTypable(_,_,_)).  

ct(N):-counts(N,genClosedTypable(_,_,_)). % 0,0,1,1,2,5,13,27,74,198,508
bt(N):-times(N,genClosedTypable(_,_,_)).
st(N):-show(N,genClosedTypable(_,_,_)).  

cn(N):-counts(N,genNF(_,_)). % 0,1,2,4,8,17,38,89,216,539,1374
bn(N):-times(N,genNF(_,_)).
sn(N):-show(N,genNF(_,_)). 

ctn(N):-counts(N,genClosedTypableNF(_,_,_)). % 0,0,1,1,2,3,7,11,25,52,110
btn(N):-times(N,genClosedTypableNF(_,_,_)).
stn(N):-show(N,genClosedTypableNF(_,_,_)). 


% rpnf(N):-relcounts(N,genClosedTypable(_,_,_),genClosedTypableNF(_,_,_)).

rp(N):-relcounts(N,genLambda(_,_),genClosedTypable(_,_,_)).

rn(N):-relcounts(N,genNF(_,_),genClosedTypableNF(_,_,_)).



rgen:-time(ranTypable(X,T,Size,Steps)),
   ppp(term=X),ppp(type=T),ppp(size(Size)+steps(Steps)),
   fail.
/*
?- rgen.
% 133,503,909 inferences, 18.883 CPU in 18.915 seconds (100% CPU, 7069881 Lips)
term=l(l(l(a(l(l(a(a(l(a(l(l(l(0))),a(0,l(a(a(l(l(l(l(0)))),0),s(s(0))))))),0),a(a(s(s(s(0))),0),a(l(l(s(0))),l(a(l(a(l(0),l(l(l(l(l(a(l(a(0,l(0))),a(l(a(l(l(l(a(0,s(s(0)))))),0)),l(l(l(l(0))))))))))))),a(a(0,l(a(a(l(l(0)),l(0)),l(0)))),l(0))))))))),l(l(a(l(a(l(l(l(a(0,l(0))))),a(a(a(a(l(l(l(a(0,l(0))))),l(0)),s(0)),l(0)),a(0,a(s(s(s(s(0)))),a(l(l(0)),a(0,l(0)))))))),0)))))))
type=(A->(((B->C->D->D)->B->C->D->D)->(E->((F->G->G)->(H->H)->I)->J->K->L->M->N->((O->P->Q->R->R)->S)->S)->E->((F->G->G)->(H->H)->I)->J->K->L->M->N->((O->P->Q->R->R)->S)->S)->T->((B->C->D->D)->B->C->D->D)->U->U)
size(136)+steps(4803158)
*/

% content of helper file stats.pl included to make this self contained

% helpers
      
% to unary base
n2s(0,0).
n2s(N,s(X)):-N>0,N1 is N-1,n2s(N1,X).

% constructor counters

inits(Cs):-maplist(init,Cs).

init(C):-flag(C,_,0).
inc(C):-flag(C,X,X+1).
inc(C,K):-flag(C,X,X+K).
total(C,R):-flag(C,R,R).


      
% counts solutions up to M
ncounts(M,Goal):-counts((=),M,Goal,_).

counts(M,Goal):-counts(n2s,M,Goal,_).

counts(Transformer,M,Goal,Ts):-
  functor(Goal,F,_),writeln(F:M),
  findall(T,(
     between(0,M,N),
       call(Transformer,N,S),
       arg(1,Goal,S),
       sols(Goal,T),
       writeln(N:T)
     ),
  Ts),
  writeln(counts=Ts),
  ratios(Ts,Rs),
  writeln(ratios=Rs).


nrelcounts(M,G1,G2):-relcounts((=),M,G1,G2).

relcounts(M,G1,G2):-relcounts(n2s,M,G1,G2).

relcounts(F,M,G1,G2):-
  counts(F,M,G1,Cs1),
  counts(F,M,G2,Cs2),
  ratios2(Cs1,Cs2,Rs),
  functor(G1,F1,_),
  functor(G2,F2,_),
  writeln(F1=Cs1),
  writeln(F2=Cs2),
  writeln(F1/F2=Rs).

% counts how many times a goal succeeds
sols(Goal, Times) :-
        Counter = counter(0),
        (   Goal,
            arg(1, Counter, N0),
            N is N0 + 1,
            nb_setarg(1, Counter, N),
            fail
        ;   arg(1, Counter, Times)
        ).
  
% benchmarks Goal up to M    
times(M,Goal):-
  between(0,M,N),
  times1(N,Goal).

times1(N,Goal):-n2s(N,S),ntimes1(N,S,Goal).


ntimes(M,Goal):-
 between(0,M,N),
 ntimes1(N,N,Goal).
 
ntimes1(N,S,Goal):-arg(1,Goal,S),
  functor(Goal,F,_),
  time(sols(Goal,Count)),writeln(N:F=count:Count),
  fail.
  
% computes rations between consecutive terms in a sequence
ratios([X|Xs],Rs):-
  map_ratio(Xs,[X|Xs],Rs).

map_ratio([],[_],[]).
map_ratio([X|Xs],[Y|Ys],[R|Rs]):-
  (Y=:=0->R=X/Y;R is X/Y),
  map_ratio(Xs,Ys,Rs).


ratios2([],[],[]).
ratios2([X|Xs],[Y|Ys],[R|Rs]):-
  (Y=:=0->R=X/Y;R is X/Y),
  ratios2(Xs,Ys,Rs).
  
  
% generates and shows terms of size N
show(N,Goal):-
 n2s(N,S),
 nshow(S,Goal).
 
nshow(S,Goal):- 
  functor(Goal,F,_),
  writeln(F),
 
  arg(1,Goal,S),
    Goal,
    show_one(Goal),
  fail.

% shows a term with renamed variables
show_one(Goal):-
  numbervars(Goal,0,_),
  Goal=..[_,_|Xs],
    member(X,Xs),
    writeln(X),
  fail
; nl.

nv(X):-numbervars(X,0,_).

ppp(X):-nv(X),writeln(X),fail.
ppp(_).



