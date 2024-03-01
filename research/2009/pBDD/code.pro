if_then_else(X,Y,Z,R):-bit(X),bit(Y),bit(Z),
  ( X==1->R=Y
  ; R=Z
  ).

bit(0).
bit(1).

% maps variable K in [0..NbOfBits-1] to Xk
var_to_bitstring_int(NbOfBits,K,Xk):-
  all_ones_mask(NbOfBits,Mask),
  var_to_bitstring_int(NbOfBits,Mask,K,Xk).

var_to_bitstring_int(NbOfBits,Mask,K,Xk):-
  NK is NbOfBits-(K+1),
  D is (1<<(1<<NK))+1,
  Xk is Mask//D.
  
% represents constant 1 as 11...1 build with NbOfBits bits 
all_ones_mask(NbOfBits,Mask):-Mask is (1<<(1<<NbOfBits))-1.   

shannon_split(NV,X, Hi,Lo):-
  all_ones_mask(NV,M),NV1 is NV-1,
  all_ones_mask(NV1,LM),
  HM is xor(M,LM),
  Lo is /\(LM,X),H is /\(HM,X),
  Hi is H>>(1<<NV1).

shannon_fuse(NV,Hi,Lo, X):-
  NV1 is NV-1,
  H is Hi<<(1<<NV1),
  X is \/(H,Lo).

% NV=number of variables, TT=a truth table, BDD the result
shannon_tree(NV,TT, st(NV,BDD)):-
  Max is (1<<(1<<NV)),
  TT<Max,
  shannon_unfold(NV,NV,TT, BDD).

% recurses to depth NV, splitting TT into pairs
shannon_unfold(0,_,TT,c(TT)).
shannon_unfold(N,NV,TT,mux(X,H,L)):-N>0,
  N1 is N-1,
  X is NV-N,
  shannon_split(N,TT,Hi,Lo),
  shannon_unfold(N1,NV,Hi,H),
  shannon_unfold(N1,NV,Lo,L).

cantor_pair(K1,K2,P):-P is (((K1+K2)*(K1+K2+1))//2)+K2.

cantor_unpair(Z,K1,K2):-
  I is floor((sqrt(8*Z+1)-1)/2),
  K1 is ((I*(3+I))//2)-Z,
  K2 is Z-((I*(I+1))//2).

pepis_pair(X,Y,Z):-pepis_J(X,Y,Z).

pepis_unpair(Z,X,Y):-pepis_K(Z,X),pepis_L(Z,Y).
 
pepis_J(X,Y, Z):-Z is ((1<<X)*((Y<<1)+1))-1.
pepis_K(Z, X):-Z1 is Z+1,two_s(Z1,X).
pepis_L(Z, Y):-Z1 is Z+1,no_two_s(Z1,N),Y is (N-1)>>1. 

two_s(N,R):-even(N),!,H is N>>1,two_s(H,T),R is T+1.
two_s(_,0).

no_two_s(N,R):-two_s(N,T),R is N // (1<<T).

even(X):- 0 =:= /\(1,X).
odd(X):- 1 =:= /\(1,X).

bitpair(X,Y,P):-
  to_rbits(X,Xs),
  to_rbits(Y,Ys),
  bitmix(Xs,Ys,Ps),!,
  from_rbits(Ps,P).

bitunpair(P,X,Y):-
  to_rbits(P,Ps),
  bitmix(Xs,Ys,Ps),!,
  from_rbits(Xs,X),
  from_rbits(Ys,Y).

bitmix([X|Xs],Ys,[X|Ms]):-!,bitmix(Ys,Xs,Ms).
bitmix([],[X|Xs],[0|Ms]):-!,bitmix([X|Xs],[],Ms).
bitmix([],[],[]).


bitpair(X-Y,Z):-bitpair(X,Y,Z).

bitunpair(Z,X-Y):-bitunpair(Z,X,Y).

unPairingTree(NV,TT, bdd(NV,UnPairingTree)):-
  Max is (1<<(1<<NV)), TT<Max,
  isplit(NV,TT, UnPairingTree).

isplit(0,TT,c(TT)).
isplit(NV,TT,ite(NV1,H,L)):-NV>0,
  NV1 is NV-1,
  bitunpair(TT,Hi,Lo),
  isplit(NV1,Hi,H),
  isplit(NV1,Lo,L).

uTreeReduce(BDD,bdd(NV,R)):-nonvar(BDD),BDD=bdd(NV,X),uTreeReduce1(X,R).

uTreeReduce1(c(TT),c(TT)).
uTreeReduce1(ite(_,A,B),R):-A==B,uTreeReduce1(A,R).
uTreeReduce1(ite(X,A,B),ite(X,RA,RB)):-A\==B,
  uTreeReduce1(A,RA),uTreeReduce1(B,RB).

reducedUnpairingTree(NV,TT, ReducedBDD):-
  unPairingTree(NV,TT, BDD),
  uTreeReduce(BDD,ReducedBDD).

pairingTree(bdd(_,X),TT):-pairingTree1(X,TT).

pairingTree1(c(TT),TT).
pairingTree1(ite(_,L,R),TT):-
  pairingTree1(L,X),
  pairingTree1(R,Y),
  bitpair(X,Y,TT).

ev(bdd(NV,B),TT):-
  all_ones_mask(NV,M),
  eval_with_mask(NV,M,B,TT).

evc(0,_,0).
evc(1,M,M).

eval_with_mask(_,M,c(X),R):-evc(X,M,R).
eval_with_mask(NV,M,ite(X,T,E),R):-
  eval_with_mask(NV,M,T,A),
  eval_with_mask(NV,M,E,B),
  var_to_bitstring_int(NV,M,X,V),
  ite(V,A,B,R).

ite(X,T,E, R):-R is xor(/\(X,xor(T,E)),E).

bsum(0,0).
bsum(N,S):-N>0,N1 is N-1,bsum1(N1,S).

bsum1(0,2).
bsum1(N,S):-N>0,N1 is N-1,bsum1(N1,S1),S is S1+(1<<(1<<N)).

bsum(S):-nat(N),bsum(N,S).

nat(0).
nat(N):-nat(N1),N is N1+1.

to_bsum(N, X,N_M):-
  nat(X),bsum(X,S),S>N,!,
  K is X-1,
  bsum(K,M),
  N_M is N-M.

nat2unPairingTree(N,BDD):-to_bsum(N, K,N_M),unPairingTree(K,N_M,BDD).

nat2bdd(N,BDD):-to_bsum(N, K,N_M),reducedUnpairingTree(K,N_M,BDD).

unPairingTree2nat(bdd(NumberOfVars,BDD),N) :-
  B=bdd(NumberOfVars,BDD),
  pairingTree(B,Nth),
  K is NumberOfVars-1,
  bsum(K,S),N is S+Nth.

bdd2nat(bdd(NumberOfVars,BDD),N) :-
  B=bdd(NumberOfVars,BDD),
  ev(B,Nth),
  K is NumberOfVars-1,
  bsum(K,S),N is S+Nth.  

unPairingTree(BDD):-nat(N),nat2unPairingTree(N,BDD).

bdd(BDD):-nat(N),nat2bdd(N,BDD).

ranbdd(NumberOfVars,BDD):-ranbdd(NumberOfVars,NumberOfVars,BDD).

ranbdd(MinVars,MaxVars,BDD):-
  MinVars1 is MinVars-1,
  bsum(MinVars1,Lower),
  bsum(MaxVars,Upper),
  Dif is Upper-Lower,
  ranint(Dif,Ran),
  N is Lower+Ran,
  nat2bdd(N,BDD).
  
ranint(Max,N):-random(X),N is floor(Max*X).

% converts an int to a list of bits, least significant first
to_rbits(0,[]).
to_rbits(N,[B|Bs]):-N>0,B is N mod 2, N1 is N//2,
  to_rbits(N1,Bs).

% converts a list of bits (least significant first) into an int
from_rbits(Rs,N):-nonvar(Rs),from_rbits(Rs,0,0,N).

from_rbits([],_,N,N).
from_rbits([X|Xs],E,N1,N3):-NewE is E+1,N2 is X<<E+N1,
  from_rbits(Xs,NewE,N2,N3).

