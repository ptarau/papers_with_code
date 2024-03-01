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

