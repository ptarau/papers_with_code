% finite functions expressed as equality 
% mapping between 2 lists of logic variables

functions_from([],_).
functions_from([V|Vs],Us):-member(V,Us),functions_from(Vs,Us).

% converts an int N into a unique hypergraph on  [0..k] 
% where k is the ceiling log of the log of N

int2hg(N,Ess):-
  int2exps(N,Es),
  map(int2exps,Es,Ess).

% maps a number to a HFS
% constructively computes a reverse for Ackermann's
% encoding from HFS to positive ints

int2hfs(N,H):-int2exps(N,Es),map2exps(Es,H).

map2exps([],[]).
map2exps([E|Es],[H|Hs]):-int2hfs(E,H),map2exps(Es,Hs).

% maps an int to a list of exponents of 2
int2exps(N,Es):-int2rbits(N,Bs),rbits2exps(Bs,Es).

% maps a list of exponents of 2 to an int
exps2int(Es,N):-exps2int(Es,0,N).

exps2int([],N,N).
exps2int([E|Es],N1,N3):-exp2(E,I),N2 is N1+I,exps2int(Es,N2,N3).

/* generalizations of Ackerman's encoding of 
   hereditarily finite sets as (large) ints, and back
   for the case of N urelements represented as
   (small) ints
*/

% int to tree of 0,1,...MaxUr urelements

int2ur(N,Ur):-int2ur(N,2,Ur).

int2ur(Ur,MaxUr,Ur):-Ur<MaxUr,!.
int2ur(N,MaxUr,UrTree):-
  int2exps(N,Es),
  ints2urs(Es,MaxUr,UrTree).

ints2urs([],_,[]).
ints2urs([E|Es],MaxUr,[U|Us]):-
  int2ur(E,MaxUr,U),
  ints2urs(Es,MaxUr,Us).

% same as int2ur/3 but with Bits indicating MaxUr=2^Bits
exp2ur(N,Bits,Ur):-exp2(Bits,MaxUr),int2ur(N,MaxUr,Ur).

% urelement tree to int

ur2int(Ur,Ur):-integer(Ur),!.
ur2int(UrTree,N):-
  urs2ints(UrTree,Es),
  exps2int(Es,N).

urs2ints([],[]).
urs2ints([U|Us],[E|Es]):-
  ur2int(U,E),
  urs2ints(Us,Es).

% computes the value of a urelement seen as a function

eval_ur(Ur,I,O):-
  ur2int(Ur,N),
  eval_tt(N,I,O).

eval_tt(TT,I,O):-
 int2rbits(TT,Bs),
 nth_member(O,Bs,I).

% some circuits represented as []-hfs

eplus(A,B,C):-C is A+(B<<1).
bs2i(Bs,N):-foldr(eplus,0,Bs,N).

ueval(Ur,R):-integer(Ur),!,R=Ur.
%ueval(Ur,R):-map(ulift,Ur,Rs),sum(Rs,R).
ueval(Urs,R):-uevals(Urs,0,R).

ulift(Ur,R):-ueval(Ur,E),exp2(E,R).

uevals([],R,R).
uevals([Ur|Urs],R1,R3):-
  ulift(Ur,R),
  R2 is R1+R,
  uevals(Urs,R2,R3).

% same with bits ????


bueval(Ur,Bits,R,Bs):-integer(Ur),!,R=Ur,padurb(Ur,Bits,Bs).
bueval(Urs,Bits,R,Bs):-buevals(Urs,Bits,0,R,Bs).

bulift(Ur,Bits,R,Bs):-bueval(Ur,Bits,E,Bs),exp2(E,R).

buevals([],_Bits,R,R,[]).
buevals([Ur|Urs],Bits,R1,R3,[Bs|Bss]):-
  bulift(Ur,Bits,R,Bs),
  R2 is R1+R,
  buevals(Urs,Bits,R2,R3,Bss).

% int to tree of 0,1,...MaxUr urelements

int2urb(N,Ur):-int2urb(N,2,Ur).

padurb(Ur,Bits,R):-
  %ilog2n(MaxUr,Bits),
  int2rbits(Ur,Bs0),
  rpad_bits_to(Bits,Bs0,Bs),
  R=..[f|Bs].

int2urb(Ur,MaxUrBits,R):-
  exp2(MaxUrBits,MaxUr),
  Ur<MaxUr,
  !,
  padurb(Ur,MaxUrBits,R).
int2urb(N,MaxUrBits,UrTree):-
  int2exps(N,Es),
  ints2urbs(Es,MaxUrBits,UrTree).

ints2urbs([],_,[]).
ints2urbs([E|Es],MaxUrBits,[U|Us]):-
  int2urb(E,MaxUrBits,U),
  ints2urbs(Es,MaxUrBits,Us).

% end
