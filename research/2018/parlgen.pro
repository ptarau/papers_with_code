% LOPSTR'16
:-ensure_loaded(library(lists)).

motzkin(S,X):-motzkin(X,S,0).

motzkin(v)-->[].
motzkin(l(X))-->down,motzkin(X).
motzkin(a(X,Y))-->down,motzkin(X),motzkin(Y).

down(s(X),X).

n2s(0,0).
n2s(N,s(X)):-N>0,N1 is N-1,n2s(N1,X).

lambda(S,X):-lambda(X,[],S,0).

lambda(v(V),Vs)-->{member(V,Vs)}.
lambda(l(V,X),Vs)-->down,lambda(X,[V|Vs]).
lambda(a(X,Y),Vs)-->down,lambda(X,Vs),lambda(Y,Vs).

type_skel(S,T,Vs):-type_skel(T,Vs,[],S,0).

type_skel(V,[V|Vs],Vs)-->[].
type_skel((X->Y),Vs1,Vs3)-->down,type_skel(X,Vs1,Vs2),type_skel(Y,Vs2,Vs3).

mpart_of([],[]).
mpart_of([U|Xs],[U|Us]):-mcomplement_of(U,Xs,Rs),mpart_of(Rs,Us).

mcomplement_of(_,[],[]).
mcomplement_of(U,[X|Xs],NewZs):-mcomplement_of(U,Xs,Zs),mplace_element(U,X,Zs,NewZs).

mplace_element(U,U,Zs,Zs).
mplace_element(_,X,Zs,[X|Zs]).

partitions(S,Ps):-len(Ps,S),mpart_of(Ps,_).

len([],0).
len([_|Vs],s(L)):-len(Vs,L).

maybe_type(L,T,Us):-type_skel(L,T,Vs),mpart_of(Vs,Us).

infer_type((v(XT)),v(X),T):-unify_with_occurs_check(XT,X:T).
infer_type(l((X:TX),A),l(X,NewA),(TX->TA)):-infer_type(A,NewA,TA).
infer_type(a(A,B),a(X,Y),TY):-infer_type(A,X,(TX->TY)),infer_type(B,Y,TX).

lamb_with_type(S,X,T):-lambda(S,XT),infer_type(XT,X,T).

typed_lambda(S,X,T):-typed_lambda(_XT,X,T,[],S,0).

typed_lambda(v(V:T),v(V),T,Vs)--> {
   member(V:T0,Vs),
   unify_with_occurs_check(T0,T)
  }.
typed_lambda(l(X:TX,A),l(X,NewA),(TX->TY),Vs)-->down,
  typed_lambda(A,NewA,TY,[X:TX|Vs]).   
typed_lambda(a(A,B),a(NewA,NewB),TY,Vs)-->down,
  typed_lambda(A,NewA,(TX->TY),Vs),
  typed_lambda(B,NewB,TX,Vs).

inhabited_type(X,Vs,N,N):-
  member(V,Vs),
  unify_with_occurs_check(X,V).
inhabited_type((X->Xs),Vs,s(N1),N2):-
  inhabited_type(Xs,[X|Vs],N1,N2).  
inhabited_type(Xs,Vs,s(N1),N3):-
  inhabited_type((X->Xs),Vs,N1,N2),
  inhabited_type(X,Vs,N2,N3).

inhabited_type(S,T):-inhabited_type(T,[],S,0).

normal_form(S,T):-normal_form(T,[],S,0).

normal_form(v(X),Vs)-->{member(X,Vs)}.
normal_form(l(X,A),Vs)-->down,normal_form(A,[X|Vs]).
normal_form(a(v(X),B),Vs)-->down,normal_form(v(X),Vs),normal_form(B,Vs).  
normal_form(a(a(X,Y),B),Vs)-->down,normal_form(a(X,Y),Vs),normal_form(B,Vs). 

nf_with_type(S,X,T):-normal_form(S,XT),infer_type(XT,X,T).

typed_nf(S,X,T):-typed_nf(_XT,X,T,[],S,0).

typed_nf(v(V:T),v(V),T,Vs)--> {
   member(V:T0,Vs),
   unify_with_occurs_check(T0,T)
  }.
typed_nf(l(X:TX,A),l(X,NewA),(TX->TY),Vs)-->down,
  typed_nf(A,NewA,TY,[X:TX|Vs]).   
typed_nf(a(v(A),B),a(NewA,NewB),TY,Vs)-->down,
  typed_nf(v(A),NewA,(TX->TY),Vs),
  typed_nf(B,NewB,TX,Vs).
typed_nf(a(a(A1,A2),B),a(NewA,NewB),TY,Vs)-->down,
  typed_nf(a(A1,A2),NewA,(TX->TY),Vs),
  typed_nf(B,NewB,TX,Vs).

hypo(X,P,Ps):-member(X:Q,Ps),unify_with_occurs_check(P,Q).

add_hypo(X,P,Ps,(hypo(X,P,Ps),Gs),Gs).

typed(X,P,[Q|Ps],N,N)-->add_hypo(X,P,[Q|Ps]).
typed(l(X,A),(P->Q),Ps,s(N1),N2)-->typed(A,Q,[X:P|Ps],N1,N2).  
typed(a(A,B),Q,Ps,s(N1),N3)--> 
  typed(A,(P->Q),Ps,N1,N2),
  typed(B,P,Ps,N2,N3).

typed(N,X:T,Gs):-n2s(N,S),typed(X,T,[],S,0,Gs,true).

typed(N,X:T):-typed(N,X:T,Gs),call(Gs).

tnf(N,X:T):-tnf(N,X:T,Gs),Gs.

tnf(N,X:T,Gs):-n2s(N,S),tnf(X,T,[],S,0,Gs,true).

tnf(X,P,Ps,N1,N2)-->tnf_no_left_lambda(X,P,Ps,N1,N2).
tnf(l(X,A),(P->Q),Ps,s(N1),N2)-->tnf(A,Q,[X:P|Ps],N1,N2).  

tnf_no_left_lambda(X,P,[Q|Ps],N,N)-->add_hypo(X,P,[Q|Ps]).
tnf_no_left_lambda(a(A,B),Q,Ps,s(N1),N3)--> 
  tnf_no_left_lambda(A,(P->Q),Ps,N1,N2),
  tnf(B,P,Ps,N2,N3).

   
% types with inhabitants in normal form, directly
inh_nf_direct(N,T):-n2s(N,S),inh_nf_direct(T,[],S,0).

inh_nf_direct_with_succ(S,T):-inh_nf_direct(T,[],S,0).

inh_nf_direct(P,Ps,N1,N2):-inh_nf_no_left_lambda_direct(P,Ps,N1,N2).
inh_nf_direct((P->Q),Ps,s(N1),N2):-inh_nf_direct(Q,[P|Ps],N1,N2).  

inh_nf_no_left_lambda_direct(P,[Q|Ps],N,N):-hypo_type(P,[Q|Ps]).
inh_nf_no_left_lambda_direct(Q,Ps,s(N1),N3) :-
  inh_nf_no_left_lambda_direct((P->Q),Ps,N1,N2),
  inh_nf_direct(P,Ps,N2,N3).

inh_nf_direct(N,T,true):-inh_nf_direct(N,T).

sols(Goal,SolCount):-aggregate_all(count,Goal,SolCount).    

concur_gen(Exec,Gen,Sols):-
  findall(Exec,Gen,Execs),
  concurrent_maplist(sols,Execs,AllSols),
  sum_list(AllSols,Sols).

sliced_gen(SliceSize,Exec,Gen,TotalSols):-
  aggregate_all(sum(Sum),
  (
    findnsols(SliceSize,Exec,Gen,Execs),
    concurrent_maplist(sols,Execs,Sols),
    sum_list(Sols,Sum)
  ),
  TotalSols).  

sliced_gen(Exec,Gen,TotalSols):-
  SliceSize is 2^20,
  sliced_gen(SliceSize,Exec,Gen,TotalSols).

thread_count(ThreadCnt):-
  prolog_flag(cpu_count,MaxThreads), 
  ThreadCnt is max(2,ceiling((2/3)*MaxThreads)).

nondet_worker():-
  thread_self(Queue),
  C=c_(0),
  repeat,
    thread_get_message(Queue,Goal),
    ( Goal='$stop',!,arg(1,C,K),thread_exit(K)
    ; Goal,
      ctr_inc(C),
      fail
    ). 
    
ctr_inc(C):-arg(1,C,K),succ(K,SK),nb_setarg(1,C,SK).

nondet_gen(ThreadCnt,MaxMes,StackLimit,Exec,ExecGen, Res):-  
  % create and start ThreadCnt  worker threads
  findall(Id,
    (
      between(1,ThreadCnt,_),
      thread_create(nondet_worker(),Id,[
        queue_max_size(MaxMes),
        stack_limit(StackLimit)
      ])
    ),
  Ids),
  ThreadArray=..[thread|Ids],  
  Ctr=c(1),
  ( call(ExecGen),
    % uniformly distribute tasks
    next_thread_id(MaxMes,Ctr,ThreadCnt,ThreadArray,Id),
    thread_send_message(Id,Exec),
    fail
  ; % send as many stops as threads, but AFTER the work is done
    forall(member(Id,Ids),thread_send_message(Id,'$stop'))
  ),
  maplist(thread_join,Ids,Rs),
  maplist(arg(1),Rs,Ks), % collect results
  sum_list(Ks,Res). % sum-them up

next_thread_id(MaxMes,Ctr,ThreadCnt,ThreadArray,Id):-
  repeat,
    arg(1,Ctr,K),succ(K,SK),
    NewK is SK mod MaxMes,
    I is 1+(K mod ThreadCnt),
    nb_setarg(1,Ctr,NewK),
    arg(I,ThreadArray,Id),
    queue_size(Id,Size),
    Size<MaxMes,
  !.

nondet_gen(Exec, ExecGen, SolCount):-
 thread_count(ThreadCnt),
 MaxMes=1000000,
 prolog_flag(stack_limit,StackLimit),
 nondet_gen(ThreadCnt, MaxMes, StackLimit, Exec, ExecGen, SolCount).

rotate(Ctr,M,K):-arg(1,Ctr,K),succ(K,SK),NewK is SK mod M,nb_setarg(1,Ctr,NewK).  

indep_task(F,N,M,I, Res):-
  Rotor=r(0),Ctr=c(0),
  ( call(F,N,_,Gs),
    rotate(Rotor,M,J),
    I=:=J, % only execute Gs for designated value I, fail otherwise
    call(Gs),
    ctr_inc(Ctr),
    fail
  ; arg(1,Ctr,Res)
  ).

indep_worker(F,N,M,I):-
  indep_task(F,N,M,I, Res),
  thread_exit(Res).

indep_run(F,N,ThreadCnt,Res):-
  M is ThreadCnt-1,
  findall(Id,
    (
      between(0,M,I), 
      thread_create(indep_worker(F,N,M,I),Id,[])
    ),
  Ids),
  maplist(thread_join,Ids,Es),
  maplist(arg(1),Es,Rs),
  sum_list(Rs,Res).

indep_run(F,N,Res):-
  thread_count(ThreadCnt),
  indep_run(F,N,ThreadCnt,Res).

indep_gen(Exec,Gen,SolCount):-Gen=..[F,N,_,Exec],indep_run(F,N,SolCount).

parRun(N,Prog,Runner,SolCount,Time):-
  Gen=..[Prog,N,_,Exec],
  time(call(Runner,Exec,Gen,SolCount),Time).

mparRun(N,Prog,SolCount,Time):-parRun(N,Prog,nondet_gen,SolCount,Time).

iparRun(N,Prog,SolCount,Time):-parRun(N,Prog,indep_gen,SolCount,Time).

concRun(N,Prog,SolCount,Time):-parRun(N,Prog,concur_gen,SolCount,Time).

slicedRun(N,Prog,SolCount,Time):-parRun(N,Prog,sliced_gen,SolCount,Time).

seqRun(N,Prog,SolCount,Time):-
  Gen=..[Prog,N,_,Exec],
  time(sols((Gen,Exec),SolCount),Time).

inh_nf(N,T,Gs):-n2s(N,S),inh_nf(T,[],S,0,Gs,true).

inh_nf(P,Ps,N1,N2)-->inh_nf_no_left_lambda(P,Ps,N1,N2).
inh_nf((P->Q),Ps,s(N1),N2)-->inh_nf(Q,[P|Ps],N1,N2).  

inh_nf_no_left_lambda(P,[Q|Ps],N,N) --> add_hypo_type(P,[Q|Ps]).
inh_nf_no_left_lambda(Q,Ps,s(N1),N3) --> 
  inh_nf_no_left_lambda((P->Q),Ps,N1,N2),
  inh_nf(P,Ps,N2,N3).

add_hypo_type(P,Ps,(hypo_type(P,Ps),Gs),Gs).

hypo_type(P,Ps):-member(Q,Ps),unify_with_occurs_check(P,Q).  

 
% helpers
      
      
% counts solutions up to M
counts(M,Goal):-
  functor(Goal,F,_),writeln(F:M),
  findall(T,(between(1,M,N),n2s(N,S),arg(1,Goal,S),sols(Goal,T),writeln(N:T)),Ts),
  writeln(counts=Ts),
  ratios(Ts,Rs),
  writeln(ratios=Rs).

  
% benchmarks Goal up to M    
times(M,Goal):-
  functor(Goal,F,_),writeln(F:M),
  between(1,M,N),
  n2s(N,S),arg(1,Goal,S),
  writeln(N:F),
  time((Goal,fail;true)),
  fail.

% computes rations between consecutive terms in a sequence
ratios([X|Xs],Rs):-
  map_ratio(Xs,[X|Xs],Rs).

map_ratio([],[_],[]).
map_ratio([X|Xs],[Y|Ys],[R|Rs]):-
  R is X/Y,
  map_ratio(Xs,Ys,Rs).

% generates and shows terms of size N
show(N,Goal):-
  functor(Goal,F,_),
  writeln(F:N),
  n2s(N,S),
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


cgo:-
  N=6,Gs=[cm,cl,cp,ct,clt,ctl,cit,cnf,cnt],  
  member(G,Gs),
  call(G,N),
  fail.
  
% counters

cm(N):- counts(N,motzkin(_,_)).            % A006318
cl(N):-counts(N,lambda(_,_)).                % A220894
cp(N):-counts(N,partitions(_,_)).          % A000110		Bell numbers
ct(N):-counts(N,maybe_type(_,_,_)).        % 2,10,75,728,8526,115764,1776060,30240210=B(n)*C(n)
clt(N):-counts(N,lamb_with_type(_,_,_)).   % A220471
ctl(N):-counts(N,typed_lambda(_,_,_)).       % A220471
cit(N):-counts(N,inhabited_type(_,_)).     % A220471
cnf(N):-counts(N,normal_form(_,_)).        % A224345
cnt(N):-counts(N,nf_with_type(_,_,_)).     %1,2,6,23,108,618,4092,30413,252590
ctn(N):-counts(N,typed_nf(_,_,_)).         %1,2,6,23,108,618,4092,30413,252590

cdb(N):-counts(N,genTypedDBTerm(_,_,_)).

% benchmarks

% A220894,A224345,A114851
bgo_test:-bgo(7).

bgo(N):-
  Gs=[bm,bl,bp,bt,blt,btl,bit,bnf,bnt],  
  member(G,Gs),
  call(G,N),
  fail.
  
  
bgo:-N=10,
  Gs=[bl,blt,btl,bit,btn],  
  member(G,Gs),
  call(G,N),
  fail.  

bmtab:-
   Ps=[ lambda(_,_),
        lamb_with_type(_,_,_),
        typed_lambda(_,_,_),
        inhabited_type(_,_),
        typed_nf(_,_,_)
   ],
   forall(
     member(P,Ps),
     bmtab(P)
   ).
   
infbm:-bmtab(inh_nf_direct_with_succ(_,_)).
  
bmtab(Prog):-
  cwriteln([prog,'N','Time']),
  between(5,10,N),n2s(N,S),    
    arg(1,Prog,S),
    time((Prog,fail;true),Time),
    functor(Prog,F,_),
    cwriteln([F,N,Time]),
    fail
  ; nl.

cwrite(X):-write(','),write(X).

cwriteln([X|Xs]):-write(X),
  forall(member(Y,Xs),cwrite(Y)),nl.

time(G,T):-
  statistics(walltime,[T1,_]),
  once(G),
  statistics(walltime,[T2,_]),
  T is (T2-T1)/1000.

  
bm(N):-times(N,motzkin(_,_)).
bl(N):-times(N,lambda(_,_)).
bp(N):-times(N,partitions(_,_)).
bt(N):-times(N,maybe_type(_,_,_)).
blt(N):-times(N,lamb_with_type(_,_,_)).
btl(N):-times(N,typed_lambda(_,_,_)).
bit(N):-times(N,inhabited_type(_,_)).
bnf(N):-times(N,normal_form(_,_)).
bnt(N):-times(N,nf_with_type(_,_,_)).
btn(N):-times(N,typed_nf(_,_,_)).

bdb(N):-times(N,genTypedDBTerm(_,_,_)).
  
% tools showing generated terms
  
  
  
  
sgo:-
  N=2,Gs=[sm,sl,sp,st,slt,stl,sit,snf,snt],  
  member(G,Gs),
  call(G,N),
  fail.  
    
sm(N):-show(N,motzkin(_,_)).
sl(N):-show(N,lambda(_,_)).
sp(N):-show(N,partitions(_,_)).
st(N):-show(N,maybe_type(_,_,_)).
slt(N):-show(N,lamb_with_type(_,_,_)).
stl(N):-show(N,typed_lambda(_,_,_)).
sit(N):-show(N,inhabited_type(_,_)).
snf(N):-show(N,normal_form(_,_)).
snt(N):-show(N,nf_with_type(_,_,_)).
stn(N):-show(N,typed_nf(_,_,_)).

sdb(N):-show(N,genTypedDBTerm(_,_,_)).    
    
% prints LaTeX form of a lambda term

texshow(T):-
  numbervars(T,0,_),
  texshow(T,Cs,[]),
  maplist(write,Cs),
  fail.
texshow(_).

texshow(v('$VAR'(I)))--> [x],['_'],[I].
texshow(l(('$VAR'(I)),E))-->[(' ')],[('~\\lambda ')],[x],['_'], [I],[('.')],texshow(E),[(' ')].
texshow(a(X,Y))-->[('(')],texshow(X),[('~')],texshow(Y),[(')')].

% printing variables with nicer names

nv(X):-numbervars(X,0,_).

pp(X):-nv(X),writeln(X),fail;true.
       
% some terms

scomb(l(A, l(B, l(C, a(a(v(A), v(C)), a(v(B), v(C))))))).    
  
ycomb(l(A, a(l(B, a(v(A), a(v(B), v(B)))), l(C, a(v(A), a(v(C), v(C))))))).
   

