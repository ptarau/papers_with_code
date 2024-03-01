% trace G

'+'(G):-
  pp_clause(calling_:G),
  S=s(0),
  if_any(G,
    (arg(1,S,K),
     K1 is K+1,
     change_arg(1,S,K1),
     pp_clause(exit_(K1):G)
    ),
    (
      pp_clause(failing_:G),
      fail
    )
  ).

% count and sample answers

'@'(G):-count_all_answers(G,K,T),println(answers(K,time(T))),!,(K<100->G;once(G)),pp_clause(G),fail.
'@'(G):-setof(G,G,Gs),length(Gs,K),println(distinct_answers=K),fail.
'@'(G):-println(duplicates),findall(G-G,G,GGs),keygroup(GGs,G,Fs),length(Fs,L),L>1,println(L:G),fail.

count_all_answers(G,K):-count_all_answers(G,K,_).

count_all_answers(G,K,T):-C=c(0),ctime(T1),call_and_count(G,C,K),ctime(T2),T is T2-T1.

call_and_count(G,C,_):-G,arg(1,C,X),X1 is X+1,change_arg(1,C,X1),fail.
call_and_count(_,C,K):-arg(1,C,K).

% for arg 1 of G ranging from 0 to N call G and return a list counting the answers
N*G:-
 arg(1,G,I),
 findall(K,answer_stats(I,N,G,K),Ks),
 println(Ks),fail.

answer_stats(I,N,G,K):-for(I,0,N),count_all_answers(G,K).

ino:-interactive(no).
