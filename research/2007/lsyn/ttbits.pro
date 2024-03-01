% bits and tt predicates

% FROM ints TO bits

nint2bss(L,N,Yss):-
  exp2(L,Big),
  int2lexps(Big,N,Es),
  map(int2lbits(L),Es,Yss).

% N-th power of 2
%exp2(N,L):-pow(2,N,R),integer(R,L).
exp2(N,L):-L is 1<<N.

ilog2n(N2,N):-N is 1+integer(log(2,N2)). 

int2lexps(NbOfBits,N,Es):-int2lbits(NbOfBits,N,Bs),rbits2exps(Bs,Es).

% converts an int to a list of bits 
int2bits(N,Bs):-integer(N),int2rbits(N,Rs),reverse(Rs,Bs).

int2lbits(NbOfBits,N,Bs):-int2bits(N,As),lpad_bits(NbOfBits,As,Bs).

lpad_bits(N,Bs,NewBs):-
  %N is 1<<NbOfBits,
  length(Bs,L),
  K is N-L,
  lpad_expand(K,Bs,NewBs).

lpad_expand(0,Bs,Bs).
lpad_expand(K,Bs,[0|NewBs]):-
  K>0,
  K1 is K-1,
  lpad_expand(K1,Bs,NewBs).
 
int2rbits(0,[]).
int2rbits(N,[B|Bs]):-N>0,B is N mod 2, N1 is N//2,int2rbits(N1,Bs).

rpad_bits_to(Max,Bs,NewBs):-rpad_bits_to(Max,Bs,NewBs,[]).

rpad_bits_to(0,[])-->[].
rpad_bits_to(Max,Bs)-->{Max>0,Max1 is Max-1},expand_bits(Bs,NewBs),rpad_bits_to(Max1,NewBs).

expand_bits([],[])-->[0].
expand_bits([B|Bs],Bs)-->[B].

% FROM bits TO ints

% converts a list of bits into an int
lbits2int(Bs,N):-nonvar(Bs),reverse(Bs,Rs),rbits2int(Rs,N).

rbits2int(Rs,N):-nonvar(Rs),rbits2int(Rs,0,0,N).

rbits2int([],_,N,N).
rbits2int([X|Xs],E,N1,N3):-
  NewE is E+1,
  N2 is X<<E+N1,
  rbits2int(Xs,NewE,N2,N3).

% maps reversed bits to exponents of 2 ONSET only
rbits2exps(Bs,Es):-rbits2exps(1,Bs,Es).

rbits2exps(Bit,Bs,Es):-rbits2exps(Bs,Bit,0, Es).

rbits2exps([],_,_,[]).
rbits2exps([B|Bs],Bit,E,NewEs):-
  E1 is E+1,
  rbit2exp(Bit,B,E,NewEs,Es),
  rbits2exps(Bs,Bit,E1,Es).

rbit2exp(Bit,B,_,Es,Es):-B=\=Bit.
rbit2exp(Bit,B,E,[E|Es],Es):-B=:=Bit.
        
% maps bits to elements of a set they select

rbits_mask([],[],[],[]).
rbits_mask([B|Bs],[E|Es],NewNs,NewYs):-
  rbit_mask(B,E,NewNs,Ns,NewYs,Ys),
  rbits_mask(Bs,Es,Ns,Ys).

rbit_mask(0,N,[N|Ns],Ns,Ys,Ys).
rbit_mask(1,Y,Ns,Ns,[Y|Ys],Ys).

% hamming distance based "closeness" relations

hamming_split(A,On,Off):-
  hamming_split(A,[On],[Off],OnDist,OffDist,R),
  write('in: '),lpp(A),
  write('on: '=OnDist),lpp(On),
  write('off:'=OffDist),lpp(Off),
  println(split=R).

hamming_split(A,OnSet,OffSet,OnDist,OffDist,R):-
  hamming_min(A,OnSet,OnDist),
  hamming_min(A,OffSet,OffDist),
  R is OffDist/(OnDist+OffDist).

% hamming distance variants from point to set

hamming_min(B,[A|As],S):-hamming(B,A,D),hamming_min(As,B,D,S).

hamming_min([],_,S,S).
hamming_min([A|As],B,S1,S2):-
  hamming(A,B,D),
  min(S1,D,S),
  hamming_min(As,B,S,S2).

hamming_avg(A,Bs,R):-
  hamming_sum(A,Bs,S),
  length(Bs,L),R is S/L.

hamming_sum(A,Bs,S):-hamming_sum(Bs,A,0,S).

hamming_sum([],_,S,S).
hamming_sum([A|As],B,S1,S2):-
  hamming(A,B,D),
  S is S1+D,
  hamming_sum(As,B,S,S2).

% hamming distance between points

hamming(A,B,D):-bitxor(A,B,C),bitcount(C,D).

cantor_pair(X,Y,P):-S is X+Y,Q is S*S,P is (Q+(3*X)+Y)//2.
%cantor_pair(K1,K2,P):-P is (((K1+K2)*(K1+K2+1))//2)+K2.
%cantor_pair(X,Y,P):-P is (X*X+X+2*X*Y+3*Y+Y*Y)//2.

cantor_tree(0,0).
cantor_tree(1,1).
cantor_tree(N,t(X,Y)):-N>1,cantor_unpair(N,A,B),cantor_tree(A,X),cantor_tree(B,Y).

cantor_unpair(Z,K1,K2):-I is floor((sqrt(8*Z+1)-1)/2),K1 is Z-((I*(I+1))//2),K2 is ((I*(3+I))//2)-Z.

cantor_pair:-cantor_pair(5).

cantor_pair(N):-
  for(I,0,N),
  for(J,0,N),
  cantor_pair(I,J,P),
  cantor_unpair(P,A,B),
  I==A,J==B,
  println(I+J=>P),
  fail.

cantor_unpair:-cantor_unpair(50).

cantor_unpair(N):-
  for(P,0,N),
  cantor_unpair(P,A,B),
  cantor_pair(A,B,Q),
  P==Q,
  println(P=>A+B),
  fail.

int2bxcat(N,C):-int2bxcat(N,2,C). % loops if 1 - feature !!!

int2bxcat(N,Max,C):-
  new_cat(C),
  foreach(
    int2bx(N,Max,e(A,B)),
    set_morphism_and_color(C,A,B)
  ).

% todo: use for syntehsis !!!
int2bx(N,P):-int2bx(N,2,P). % loops if 1 !!!

int2bx(N,Max,P):-N>=Max,
  bitmix_unpair(N,E1,E2),
  member(E,[E1,E2]),
  ( P=e(N,E)
  ; int2bx(E,Max,P)
  ).
  
bitmix_tree(0,0).
bitmix_tree(1,1).
bitmix_tree(N,t(X,Y)):-N>1,bitmix_unpair(N,A,B),bitmix_tree(A,X),bitmix_tree(B,Y).

/*
bitmix_eval(0,0).
bitmix_eval(1,1).
bitmix_eval(N,t(X,Y)):-N>1,bitmix_unpair(N,A,B),bitmix_tree(A,X),bitmix_tree(B,Y).
*/

bitmix_pair(N):-
  for(I,0,N),
  for(J,0,N),
  bitmix_pair(I,J,P),
  bitmix_unpair(P,A,B),
  I==A,J==B,
  println(I+J=>P),
  fail.

bitmix_unpair(N):-
  for(P,0,N),
  bitmix_unpair(P,A,B),
  bitmix_pair(A,B,Q),
  P==Q,
  println(P=>A+B),
  fail.
    
bitmix_pair(Y,X,P):-int2rbs(X,Xs),int2rbs(Y,Ys),bitmix(Xs,Ys,Ps),rbits2int(Ps,P).

bitmix_unpair(P,Y,X):-int2rbs(P,Ps),bitmix(Xs,Ys,Ps),rbits2int(Xs,X),rbits2int(Ys,Y),!.

bitmix([],[],[]).
bitmix([],[Y|Ys],[A,B|Ps]):-bitmix2(0,Y,A,B),bitmix([],Ys,Ps).
bitmix([X|Xs],[],[A,B|Ps]):-bitmix2(X,0,A,B),bitmix(Xs,[],Ps).
bitmix([X|Xs],[Y|Ys],[A,B|Ps]):-bitmix2(X,Y,A,B),bitmix(Xs,Ys,Ps).

bitmix2(X,Y,X,Y).

%bitmix2(X,Y,A,Y):-bitx(X,Y,A).
%bitmix2(X,Y,X,B):-bitx(X,Y,B).

bitx(0,0,0).
bitx(0,1,1).
bitx(1,0,1).
bitx(1,1,0).

int2rbs(N,Bs):-int2rbs(N,0,Bs).

int2rbs(0,K,Bs):-J is K mod 2,odd1ev0(J,Bs).
int2rbs(N,K,[B|Bs]):-N>0,B is N mod 2, N1 is N//2,K1 is K+1,int2rbs(N1,K1,Bs).

odd1ev0(0,[]).
odd1ev0(1,[0]).

int2graph(N,C):-
  new_cat(C),
  foreach(
    int2pairs(N,e(A,B)),
    set_morphism_and_color(C,A,B)
  ).
    
int2pairs(N,P):-int2pairs(N,_E,P).   
    
int2pairs(N,E,e(A,B)):-
  int2exps(N,Es),
  member(E,Es),
  bitmix_unpair(E,A,B).  
  
bitcount(N,BitCount):-countbits(N,0,BitCount).

% entropy of a boolean function of NbOfBits args
% given as a 0..2^(2^NbOfBits)-1 number representing
% its truth table
tt_entropy(VarNo,TT,Ones,TTLen,E):-
  exp2(VarNo,TTLen),
  exp2(TTLen,Lim),MaxTT is Lim-1,
  TT>0,TT<MaxTT,
  bitcount(TT,Ones),
  bit_entropy(Ones,TTLen,E).

bit_entropy(Ones,TotalBits,E):-
  P1 is Ones/TotalBits,
  P0 is 1-P1,
  E is -(P1*log(2,P1)+P0*log(2,P0)).
  
countbits(0,S,S).
countbits(N,S1,S2):-
  N>0,B is N mod 2, 
  N1 is N//2,
  S is S1+B,
  countbits(N1,S,S2).

% counting trees and leaf-dags

% 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796
catalan(1,1).
catalan(N1,R1):-
  N1>1,
  N is N1-1,
  catalan(N,R),
  R1 is R*(4*N+2)/(N+2).
  
leafdags(MGates,NPIs,R):-
  catalan(MGates,C),
  NbLeaves is MGates+1,
  F is pow(NPIs,NbLeaves),
  R is C*F.

funtree(NbNodes,NbPIs,T):-
  length(PIs,NbPIs),
  bintree(NbNodes,Leaves,T),
  functions_from(Leaves,PIs).

bintree(NbNodes,Leaves,T):-btree(T,NbNodes-Leaves,0-[]).

btree(Leaf)-->bleaf(Leaf).
btree(t(L,R))-->bnode,btree(L),btree(R).

bleaf(Leaf,N-[Leaf|Ls],N-Ls).

bnode(N1-Ls,N-Ls):-N1>0,N is N1-1.

% apply a tt as function to an int seen as a variable assignment

tt_apply(TT,V0_N,R):-int2exps(TT,Es),(member(V0_N,Es)->R=1;R=0).

% circuit eval algo: decompose V0_N in "parts" and see if its parts "fire" TT
