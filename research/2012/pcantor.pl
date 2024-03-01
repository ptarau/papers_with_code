cantor_pair(X1,X2,P) :- P is X1 + (((X1+X2+1) * (X1+X2)) // 2).

cantor_unpair(P,K1,K2) :- 
  E is 8*P+1,
  intSqrt(E,R),
  I is (R-1)//2,
  K1 is P-((I*(I+1))//2),
  K2 is ((I*(3+I))//2)-P.

intSqrt(0,0).
intSqrt(N,R) :- N>0,
  iterate(N,N,K),
  K2 is K*K,
  (K2>N -> R is K-1 ; R=K).

iterate(N,X,NewR) :- 
  R is (X+(N//X))//2,
  A is abs(R-X),
  (A<2 -> NewR=R ; iterate(N,R,NewR)).

binomial_loop(_,K,I,P,R) :- I>=K, !, R=P.
binomial_loop(N,K,I,P,R) :-
   I1 is I+1,
   P1 is ((N-I)*P) // I1,
   binomial_loop(N,K,I1,P1,R).

binomial(N,K,R) :- N<K, !, R=0.
binomial(N,K,R) :- K1 is N-K, K>K1, !, 
  binomial_loop(N,K1,0,1,R).
binomial(N,K,R) :- binomial_loop(N,K,0,1,R).

from_cantor_tuple1(Xs,R) :- from_cantor_tuple1(Xs,0,0,0,R).

from_cantor_tuple1([],_L,_S,B,B).
from_cantor_tuple1([X|Xs],L1,S1,B1,Bn) :- 
  L2 is L1+1,
  S2 is S1+X,
  N is S2+L1,
  binomial(N,L2,B),
  B2 is B1+B,
  from_cantor_tuple1(Xs,L2,S2,B2,Bn).

to_cantor_tuple1(K,N,Ns) :- 
  numlist(0,N,Is),
  cartesian_power(K,Is,Ns),
  from_cantor_tuple1(Ns,N),
  !. % just an optimization - no other solutions exists

cartesian_power(0,_,[]). 
cartesian_power(K,Is,[X|Xs]) :- K>0,
  K1 is K-1,
  member(X,Is),
  cartesian_power(K1,Is,Xs).

largest_binomial_sum(K,M,R) :- largest_binomial_sum(K,M,0,R).

largest_binomial_sum(0,_,R,R).
largest_binomial_sum(K,M,R1,Rn) :- K>0, K1 is K-1,
  M1 is M+K1,
  binomial(M1,K,B),
  R2 is R1+B,
  largest_binomial_sum(K1,M,R2,Rn).

find_hyper_plane(0,_,0).
find_hyper_plane(K,N,M) :- K>0,
  between(0,N,M),
  largest_binomial_sum(K,M,R),
  R>=N,
  !.

to_cantor_tuple2(K,N,Ns) :- 
 find_hyper_plane(K,N,M),
 sum_bounded_cartesian_power(K,M,Xs),
 from_cantor_tuple1(Xs,N),
 !,
 Ns=Xs.

sum_bounded_cartesian_power(0,0,[]). 
sum_bounded_cartesian_power(K,M,[X|Xs]) :-  K>0, M>=0,
  K1 is K-1,
  between(0,M,X),
  M1 is M-X,
  sum_bounded_cartesian_power(K1,M1,Xs).

list2set(Ns,Xs) :- list2set(Ns,-1,Xs).

list2set([],_,[]).
list2set([N|Ns],Y,[X|Xs]) :- X is (N+Y)+1, list2set(Ns,X,Xs).

set2list(Xs,Ns) :- set2list(Xs,-1,Ns).

set2list([],_,[]).
set2list([X|Xs],Y,[N|Ns]) :- N is (X-Y)-1, set2list(Xs,X,Ns).

from_cantor_tuple(Ns,N) :- 
  list2set(Ns,Xs),
  untupling_loop(Xs,0,0,N).

untupling_loop([],_L,B,B).
untupling_loop([X|Xs],L1,B1,Bn) :- 
  L2 is L1+1,
  binomial(X,L2,B),
  B2 is B1+B,
  untupling_loop(Xs,L2,B2,Bn).

tupling_loop(0,_,[]).
tupling_loop(K,N,[D|Ns]) :- K>0,
  NewK is K-1,
  I is K+N,
  between(NewK,I,M),
  binomial(M,K,B),
  B>N,
  !, % no more search is needed
  D is M-1, % the previous binomial gives the "digit" D
  binomial(D,K,BM),
  NewN is N-BM,
  tupling_loop(NewK,NewN,Ns).

to_cantor_tuple(K,N,Ns) :- 
  tupling_loop(K,N,Xs),
  reverse(Xs,Rs),
  set2list(Rs,Ns).

from_cantor_set_tuple(Xs,N) :- untupling_loop(Xs,0,0,N).

to_cantor_set_tuple(K,N,Xs) :- 
  tupling_loop(K,N,Ts),
  reverse(Ts,Xs).

mset2set(Ns,Xs) :- mset2set(Ns,0,Xs).

mset2set([],_,[]).
mset2set([X|Xs],I,[M|Ms]) :- I1 is I+1, M is X+I, mset2set(Xs,I1,Ms).

set2mset(Xs,Ns) :- set2mset(Xs,0,Ns).

set2mset([],_,[]).
set2mset([X|Xs],I,[M|Ms]) :- I1 is I+1, M is X-I, set2mset(Xs,I1,Ms).  

from_cantor_multiset_tuple(Ms,N) :- 
  mset2set(Ms,Xs),
  from_cantor_set_tuple(Xs,N).

to_cantor_multiset_tuple(K,N,Ms) :- 
  to_cantor_set_tuple(K,N,Xs),
  set2mset(Xs,Ms).

fair_multiset_tuple_generator(From,To,Length, Tuple) :- 
  between(From,To,N),
  to_cantor_multiset_tuple(Length,N,Tuple).

to_lagrange_squares(N,Ms) :- 
  M is N^2, % conservative upper limit
  fair_multiset_tuple_generator(0,M,4,Ms),
  maplist(square,Ms,MMs),
  sumlist(MMs,N),
  !. % keep the first solution only
  
square(X,S) :- S is X*X.

% benchmark

bm :- 
  member(K-N,[5-10,5-20,5-100000,50-100000,100-100000,1000-10000000,2000-10000000]),
  bm2(K,N),
  fail
; true.

bm2(K,N) :- 
  % run this only for small values
  (K=<5,N=<30->bm1(to_cantor_tuple1,K,N);true),
  % compute inverse
  (K=<100,N=<1000000->bm1(to_cantor_tuple2,K,N);true),
  fail
; % only compute time for the direct and inverse function, for large values
  bm1(to_cantor_tuple,K,N),
  to_cantor_tuple(K,N,Ns),
  write('from_cantor_tuple on the result'),nl,
  time(from_cantor_tuple(Ns,_)),
  fail
; write('------------'),nl,nl.

bm1(InverseCantorKN,K,N) :- 
  write([InverseCantorKN,K,N]),nl,
  time(call(InverseCantorKN,K,N,_)),
  nl.

% compares unparing for K=2  
pbm :- 
  K=2,
  between(0,4,I),
  N is 10^(10+I)-1,
  write(cantor_unpair(10^(10+I)-1)),nl,
  time(cantor_unpair(N,_,_)),
  write(to_cantor_tuple(K,10^(10+I)-1)),nl,
  time(to_cantor_tuple(K,N,_)),
  write('---------------'),nl,nl,
  fail
; nl.

mset_pair(M1,M2,N):-N is M1+M2*(M2+1)//2.
set_pair(S1,S2,N):-N is S1+S2*(S2-1)//2.


/* :-[library(clpfd)]. 
% unfortunately this results in very slow code
to_cantor_tuple3(L,Z,Ns):-
 find_hyper_plane(L,Z,M),
 constrained_cartesian_power(L,M,Ms),
 constrained_list2set(L,Ms,Xs),
 constrained_untupling_loop(Xs,0,Z,0),
 label(Ms),
 !,
 Ns=Ms.

constrained_cartesian_power(0,0,[]). 
constrained_cartesian_power(K,M,[X|Xs]):-K>0,
  M #>= 0,
  K1 is K-1,
  X #>=0, X#=<M,
  M1 #= M-X,
  constrained_cartesian_power(K1,M1,Xs).
 
constrained_list2set(L,Ns,Xs):-
  length(Ns,L),
  length(Xs,L),
  all_different(Xs),
  constrained_list2set1(Ns,-1,Xs).

constrained_list2set1([],_,[]).
constrained_list2set1([X|Xs],Y,[A|As]):-
  A1 #= X+Y,
  A #= A1+1,
  constrained_list2set1(Xs,A,As).  

constrained_untupling_loop([],_L,B1,Bn):-B1#=Bn.
constrained_untupling_loop([X|Xs],L1,B1,Bn):-B1#>0,
  L2 is L1+1,
  X #=< B1,
  cbinomial(X,L2,B),
  B2 #= B1-B,
  constrained_untupling_loop(Xs,L2,B2,Bn).

cbinomial(N,K,R):-N#<K,R#=0.
cbinomial(N,K,R):-N#>=K,cbinomial_loop(N,K,0,1,R).

cbinomial_loop(_,K,I,P,R):-I#>=K,R#=P.
cbinomial_loop(N,K,I,P,R):-I#<K,
   I1 is I+1,
   N1 #= N-I,
   T #= N1*P,
   T #= P1 * I1,
   cbinomial_loop(N,K,I1,P1,R). */

