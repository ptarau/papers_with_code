synthesize_2_arg_boolean_operators:-
  synthesize_2_arg_boolean_operators(R,S),
  println(total(size=R,steps=S)).
  
synthesize_2_arg_boolean_operators(R,S):-
  synthesize_2_arg_boolean_operators(0,16,R,S).

synthesize_2_arg_boolean_operators(N,N,R,S):-!,R=0,S=0.
synthesize_2_arg_boolean_operators(N1,N2,R,S):-
  N is N1+1,
  synthesize_circuit(2:N1,UT,Size,Steps),
  pp_clause(UT),nl,
  synthesize_2_arg_boolean_operators(N,N2,R1,S1),
  R is R1+Size,
  S is S1+Steps.

rp(Bits:N):-
  MBits is 1<<Bits,
  int2rbits(N,Bs0),rpad_bits_to(MBits,Bs0,Bs),
  println(Bits:Bs),nl,
  foreach(
    nth_member(B,Bs,I1),
    ( I is I1-1,
      int2rbits(I,Is0),
      rpad_bits_to(Bits,Is0,Is),
      println(tt(I,Is=>B))
    )
  ),
  nl.  

lpp(N):-int2bits(N,Bs),println(Bs).
rpp(N):-int2rbits(N,Bs),println(Bs).

tpp(NbOfBits,N):-
  [SP,C]=" :",
  L is 1<<NbOfBits, 
  int2lbits(L,N,Bs0),
  % reverse(Bs0,Bs),
  Bs=Bs0,
  write(N),put(C),
  foreach(
    nth_member(B,Bs,I),
    ( write(B),
      if(I mod 4=:=0,put(SP),true)
    )
  ),
  nl.
  
ktest:-
 N=3,
 var_to_bitstring_int(N,0,X0),   
 var_to_bitstring_int(N,1,X1),  
 var_to_bitstring_int(N,2,X2),  
 bitite(N,X0,X1,X2,R),
 tpp(N,X0),
 tpp(N,X1),
 tpp(N,X2),
 tpp(N,R).
 
ktest1:-
 N=4,
 var_to_bitstring_int(N,0,X1),   
 var_to_bitstring_int(N,1,X2),  
 var_to_bitstring_int(N,2,X3),   
 var_to_bitstring_int(N,3,X4),  
 bitxor(X1,X3,X5),
 bitxor(X1,X2,X6),
 bitxor(X3,X4,X7),
 bitor(X5,X6,X8),
 bitxor(X6,X7,X9),
 bitnot(N,X9,X9N),
 bitand(X8,X9N,X10),
 bitite(N,X1,X2,X3,R),
 bitite(N,X3,X2,X1,RR),
 tpp(N,X1),
 tpp(N,X2),
 tpp(N,X3),
 tpp(N,X4),
 nl,
 tpp(N,X5),
 tpp(N,X6),
 tpp(N,X7),
 tpp(N,X8),
 tpp(N,X9),
 tpp(N,X10),
 tpp(N,R),
 tpp(N,RR).

% tests

ldags:-ldags(4,9).

ldags(M,N):-
  for(IM,1,M),
    nl,
    for(IN,1,N),
      leafdags(IN,IM,R),
  println(R),fail
; nl.

/*
?- ldags.

1
2
5
14
42
132
429
1430
4862

4
16
80
448
2688
16896
109824
732160
4978688

9
54
405
3402
30618
288684
2814669
28146690
287096238

16
128
1280
14336
172032
2162688
28114944
374865920
5098176512
no
*/

  