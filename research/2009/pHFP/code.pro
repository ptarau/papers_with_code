unrank_(Ulimit,_,N,R):-N>=0,N<Ulimit,!,R=N.
unrank_(Ulimit,F,N,R):-N>=Ulimit,
  N0 is N-Ulimit,
  call(F,N0,Ns),
  maplist(unrank_(Ulimit,F),Ns,R).

unrank(F)-->
  default_ulimit(Ulimit),
  unrank_(Ulimit,F).

default_ulimit(L)-->{clause(ulimit(L),_)},!.
default_ulimit(0)-->[].

rank_(Ulimit,_,N,R):-integer(N),N>=0,N<Ulimit,!,R=N.
rank_(Ulimit,G,Ts,R):-
  maplist(rank_(Ulimit,G),Ts,T),
  call(G,T,R0),
  R is R0+Ulimit.

rank(G)-->
  default_ulimit(Ulimit),
  rank_(Ulimit,G).  

set2nat(Xs,N):-set2nat(Xs,0,N).

set2nat([],R,R).
set2nat([X|Xs],R1,Rn):-R2 is R1+(1<<X),set2nat(Xs,R2,Rn).

hfs2nat-->default_ulimit(Ulimit),hfs2nat_(Ulimit).

hfs2nat_(Ulimit)-->rank_(Ulimit,set2nat).

nat2set(N,Xs):-nat2elements(N,Xs,0).

nat2elements(0,[],_K).
nat2elements(N,NewEs,K1):-N>0,
  B is /\(N,1),
  N1 is N>>1,K2 is K1+1,
  add_el(B,K1,Es,NewEs),
  nat2elements(N1,Es,K2).

add_el(0,_,Es,Es).
add_el(1,K,Es,[K|Es]).

nat2hfs_(Ulimit)-->unrank_(Ulimit,nat2set).

nat2hfs-->default_ulimit(Ulimit),nat2hfs_(Ulimit).

% factoradics of N, right to left
fr(0,[0]).
fr(N,R):-N>0,fr1(1,N,R).
   
fr1(_,0,[]).
fr1(J,K,[KMJ|Rs]):-K>0,KMJ is K mod J,J1 is J+1,KDJ is K // J,
  fr1(J1,KDJ,Rs).

fl(N,Ds):-fr(N,Rs),reverse(Rs,Ds).

lf(Ls,S):-length(Ls,K),K1 is K-1,lf(K1,_,S,Ls,[]).

% from list of digits of factoradics, back to decimals
lf(0,1,0)-->[0].
lf(K,N,S)-->[D],{K>0,K1 is K-1},lf(K1,N1,S1),{N is K*N1,S is S1+D*N}.

rf(Ls,S):-reverse(Ls,Rs),lf(Rs,S).

perm2nth(Ps,Size,N):-
  length(Ps,Size),
  Last is Size-1,
  ints_from(0,Last,Is),
  perm_lehmer(Is,Ps,Ls),
  lf(Ls,N).

% associates Lehmer code to a permutation 
perm_lehmer([],[],[]).
perm_lehmer(Xs,[X|Zs],[K|Ks]):-
  select_and_remember(X,Xs,Ys,0,K),
  perm_lehmer(Ys,Zs,Ks).

% remembers selections - for Lehmer code
select_and_remember(X,[X|Xs],Xs,K,K).
select_and_remember(X,[Y|Xs],[Y|Ys],K1,K3):-K2 is K1+1,
  select_and_remember(X,Xs,Ys,K2,K3).

nth2perm(Size,N, Ps):-
  fl(N,Ls),length(Ls,L),
  K is Size-L,
  Last is Size-1,
  ints_from(0,Last,Is),
  zeros(K,Zs),
  append(Zs,Ls,LehmerCode),
  perm_lehmer(Is,Ps,LehmerCode).

% fast computation of the sum of all factorials up to N!
sf(0,0).
sf(N,R1):-N>0,N1 is N-1,ndup(N1,1,Ds),rf([0|Ds],R),R1 is R+1.

sf(S):-nat(N),sf(N,S).

to_sf(N, K,N_M):-nat(X),sf(X,S),S>N,!,K is X-1,sf(K,M),N_M is N-M.

nat2perm(0,[]).
nat2perm(N,Ps):-to_sf(N, K,N_M),nth2perm(K,N_M,Ps).

perm2nat([],0).
perm2nat(Ps,N) :-perm2nth(Ps, Size,Nth),sf(Size,S),N is S+Nth.

nat2hfp --> default_ulimit(D),nat2hfp_(D).   
nat2hfp_(Ulimit) --> unrank_(Ulimit,nat2perm).
hfp2nat --> rank(perm2nat).

secret([[[[[]],[]],[[],[[]]]],[[[],[[]]],[[],[[]]]],[],[],[[[],[[]]],[[[]],[]]]]).

% generates integers From..To
ints_from(From,To,Is):-findall(I,between(From,To,I),Is).

% replicates X, N times
ndup(0, _,[]).
ndup(N,X,[X|Xs]):-N>0,N1 is N-1,ndup(N1,X,Xs).
  
zeros(N,Zs):-ndup(N,0,Zs).

% generator for the stream of natural numbers  
nat(0).
nat(N):-nat(N1),N is N1+1.  

show_hfs(S):-gshow(S,"{,}"),nl.
show_hfp(S):-gshow(S,"( )"),nl.

gshow(0,[L,_C,R]):-put(L),put(R).
gshow(N,_):-integer(N),N>0,!,write(N).
gshow(Hs,[L,C,R]):-put(L),gshow_all(Hs,[L,C,R]),put(R).

gshow_all([],_).
gshow_all([H],LCR):-gshow(H,LCR).
gshow_all([H,G|Hs],[L,C,R]):-
  gshow(H,[L,C,R]),
  ([C]\=="~"->put(C);true),
  gshow_all([G|Hs],[L,C,R]).

