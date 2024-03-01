% the TxT<->T bijection: pair(X,Y,Z) represents Z=2^X(2*Y+1)-1
unpair(e, e,e).
unpair(((A->B)->D), e,(C->D)) :- pair(A,B, C).
unpair((e->D), (C->B),E) :- unpair(D, A,E), unpair(A, C,B). 

pair(e,e, e).
pair(e,(C->D), ((A->B)->D)) :- unpair(C, A,B).
pair((C->B),E, (e->D)) :- pair(C,B, A), pair(A,E, D).

% successor+predecessor for finite sequences of naturals as binary trees
% intuition: (X->Y) represents 2^X*(2*Y+1)
s(Z,(X->Y)):-unpair(Z,X,Y).
p((X->Y),Z):-pair(X,Y,Z).

% infinite enumerator/stream
n(e).
n(S):-n(P),s(P,S).

% constructors for bijective base-2 view
o(X,(e->X)).
i(X,Z):-o(X,Y),s(Y,Z).
    
% recongnizers/deconstructors
o_((e->Y),Y).
i_(X,X2):-p(X,X1),o_(X1,X2).

% addition
add(e,Y,Y).
add((X->Xs),e,(X->Xs)).
add(X,Y,Z):-o_(X,X1),o_(Y,Y1),add(X1,Y1,R),i(R,Z).
add(X,Y,Z):-o_(X,X1),i_(Y,Y1),add(X1,Y1,R),s(R,S),o(S,Z).
add(X,Y,Z):-i_(X,X1),o_(Y,Y1),add(X1,Y1,R),s(R,S),o(S,Z).
add(X,Y,Z):-i_(X,X1),i_(Y,Y1),add(X1,Y1,R),s(R,S),i(S,Z).

% subtraction
sub(X,e,X).
sub(X,Y,Z):-o_(X,X1),o_(Y,Y1),sub(X1,Y1,R),o(R,R1),p(R1,Z).
sub(X,Y,Z):-o_(X,X1),i_(Y,Y1),sub(X1,Y1,R),o(R,R1),p(R1,R2),p(R2,Z).
sub(X,Y,Z):-i_(X,X1),o_(Y,Y1),sub(X1,Y1,R),o(R,Z).
sub(X,Y,Z):-i_(X,X1),i_(Y,Y1),sub(X1,Y1,R),o(R,R1),p(R1,Z).

% comparison
cmp(X,X,eq).
cmp(X,Y,lt):-sub(Y,X,(_->_)).
cmp(X,Y,gt):-sub(X,Y,(_->_)).

% double and half
double(X,Y):-pair(e,X, Y).
half(Y,X):-unpair(Y, e,X).

% multiplication
multiply(e,_,e).
multiply((_->_),e,e).
multiply((HX->TX),(HY->TY),(H->T)):-
  add(HX,HY,H),
  multiply((e->TX),TY,S),
  add(TX,S,T).

% power
power(_,e,(e->e)).
power(X,Y,Z):-o_(Y,Y1),
  multiply(X,X,X2),
  power(X2,Y1,P),
  multiply(X,P,Z).
power(X,Y,Z):-i_(Y,Y1),
  multiply(X,X,X2),
  power(X2,Y1,P),
  multiply(X2,P,Z).  

% power of 2
exp2(X,(X->e)).

% division and reminder
divide(X,Y,D):-div_and_rem(X,Y,D,_).
reminder(X,Y,R):-div_and_rem(X,Y,_,R).

div_and_rem(X,Y,e,X):-cmp(X,Y,lt).
div_and_rem(X,Y,D,R):-Y=(_->_),divstep(X,Y,QT,RM),
  div_and_rem(RM,Y,U,R),
  add((QT->e),U,D).

divstep(N,M,Q,D):-try_to_double(N,M,e,Q),
  multiply((Q->e),M,P),
  sub(N,P,D).
  
try_to_double(X,Y,K,R):-cmp(X,Y,Rel),
  try_to_double1(Rel,X,Y,K,R).
 
try_to_double1(lt,_,_,K,R):-p(K,R).
try_to_double1(Rel,X,Y,K,R):-
  member(Rel,[eq,gt]),
  double(Y,Y2),s(K,K1),
  try_to_double(X,Y2,K1,R).

% converters to/from standard integers

n2s(0,e).
n2s(X,(A->B)):-X>0,c_(X,Y,Z),n2s(Y,A),n2s(Z,B).

s2n(e,0).
s2n((X->Y),R):-s2n(X,A),s2n(Y,B),c(A,B,R).

c(X,Y,Z):-Z is 2^X*(2*Y+1).

c_(X,R,S):-X>0,
  ( X/\1=:=1 -> R=0,S is (X-1)>>1
  ; X1 is X >> 1,
    c_(X1,R1,S),
    R is 1+R1
  ). 

% tests

xy(F,A,B,C):-
  n2s(A,Xs),
  n2s(B,Ys),
  call(F,Xs,Ys,Z),
  s2n(Z,C).

x(F,A,C):-
  n2s(A,Xs),
  call(F,Xs,Zs),
  s2n(Zs,C).

y(F,A,C):-
  n2s(C,Zs),
  call(F,Xs,Zs),
  s2n(Xs,A).
  
z(F,A,B,C):-
  n2s(C,Z),
  call(F,Xs,Ys,Z),
  s2n(Xs,A),
  s2n(Ys,B).
  
% misc

syr(X,R):-add(((e->e)->X),(e->X),S),unpair(S,_,R).

nsyr(e,[e]).
nsyr(N,[N|Ns]):-N=(_->_),syr(N,K),nsyr(K,Ns).
    
c:-['gtypes.pl'].

  
  