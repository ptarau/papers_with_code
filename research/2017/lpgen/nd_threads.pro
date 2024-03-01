% thread pool mechanism for execution of 
% _nondeterministically_  generated nondeterministic goals
% a form of staged programming: a generator creates goals
% it usable to run things in constant space, nor recursion involved

nondet_run(Exec,ExecGen):-  
  thread_count(ThreadCnt),
  message_queue_create(Master,[]),
  findall(Id,
    (
      between(1,ThreadCnt,_),
      thread_create(nondet_worker(Master),Id,[])
    ),
  Ids),
  ( ExecGen,
    % send as much work as generated
    thread_send_message(Master,Exec),%ppp(sent=Exec),
    fail
  ; % send as many stops as threads, but AFTER the work is done
    forall(member(_,Ids),thread_send_message(Master,'$stop'))
  ),
  maplist(thread_join,Ids,_),
  message_queue_destroy(Master).

thread_count(ThreadCnt):-
  prolog_flag(cpu_count,MaxThreads), 
  ThreadCnt is max(2,floor((2/3)*MaxThreads)).
  
nondet_worker(Master):-
  repeat,
    thread_get_message(Master,Goal),
    ( Goal='$stop',!
    ; Goal,
      fail
    ).
      
nondet_run(Exec,ExecGen,Action):-nondet((Exec,Action),ExecGen).
% example of use and tests
  
% runs in parallel counting solutions
% uses an ExecGenerator for which runs each
% generated Goal in thread pool
       
nondet_count(Exec,ExecGen,SolCount):-
  flag(sol_count,_,0),
  nondet_run((Exec,flag(sol_count,K,K+1)),ExecGen),  
  flag(sol_count,SolCount,SolCount).
  
nondet_test:-time(nondet_test(1000)).
  
nondet_test(N):-nondet_count(between(1,N,_I),between(1,N,_J),Res),writeln(Res).

det_test:-time(det_test(1000,Res)),writeln(Res).
  
det_test(N,SolCount):-
  flag(sol_count,_,0),
  ( between(1,N,_I),
      between(1,N,_J),
        flag(sol_count,K,K+1),
        fail
  ; true
  ),
  flag(sol_count,SolCount,SolCount).
  
   