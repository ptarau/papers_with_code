% synthetizes circuit and shows first/minimal result
synthesize_circuit(BooleanExpression):-
  ctime(Time1),
  synthesize_circuit(BooleanExpression,UniqueVars:LeafDag:OutputSpec,L,Steps),
  ctime(Time2),
  !,
  Time is Time2-Time1,
  println(size(L,time:Time,steps:Steps)),
  pp_clause(UniqueVars:LeafDag==OutputSpec),
  fail.

% synthetizes circuit given as a NbOfBits
% bitstring-integer encoding of a truth table OutputSpec
% and returns a list of primary inputs PIs and a LeafDag 

synthesize_circuit(NbOfBits:OutputSpec, PIs:LeafDag:OutputSpec,GateCount,Steps):-
  integer(NbOfBits),integer(OutputSpec),
  !,
  length(UniqueBitstringIntVars,NbOfBits),
  vars_to_bitstring_ints(UniqueBitstringIntVars),
  synthesize_leaf_dag(UniqueBitstringIntVars,NbOfBits,
     PIs:LeafDag=OutputSpec,GateCount,Steps).  

% synthetizes a circuit given as an expression built with
% the 16 2-argument boolean operators and returns it as a
% LeafDag with its primary inputs PIs and its 
% bitstring-integer encoding as a truth table OutputSpec

synthesize_circuit(BooleanExpression0, PIs:LeafDag:OutputSpec,GateCount,Steps):-
  vars_of(BooleanExpression0,UniqueBitstringIntVars),
  length(UniqueBitstringIntVars,N),
  all_ones_mask(N,BigOne),
  replace_one_with(BigOne,BooleanExpression0,BooleanExpression),
  vars_to_bitstring_ints(UniqueBitstringIntVars,NbOfBits),
  eval_bitstring_int_formula(BooleanExpression,NbOfBits, OutputSpec),
  synthesize_leaf_dag(UniqueBitstringIntVars,NbOfBits,
    PIs:LeafDag=OutputSpec,GateCount,Steps).

% Synthetizes a circuit given bitstring-integer encodings of 
% unique bitstring integer represented variables and a truth
% table OutputSpec. It returns a list of 
% primary inputs PIs and a LeafDag. 

synthesize_leaf_dag(UniqueBitstringIntVars,UniqueVarAndConstCount,
                                           PIs:LeafDag=OutputSpec,GateCount,Steps):-
  ptt(UniqueBitstringIntVars,UniqueVarAndConstCount,OutputSpec), % 
  MaxLeaves is (2*UniqueVarAndConstCount)*exp2(UniqueVarAndConstCount),
  new_step_counter(StepCounter),
  constant_functions(UniqueVarAndConstCount,ICs,OCs),
  once(append(ICs,UniqueBitstringIntVars,UniqueVarsAndConsts)),
  % println(here=UniqueVarsAndConsts),
  for(LeafCount,1,MaxLeaves),
    generate_leaf_dag(UniqueVarAndConstCount,LeafCount, 
                      UniqueVarsAndConsts,ETree,StepCounter,OutputSpec),
  get_step(StepCounter,Steps), %
  decode_leaf_dag(ETree,UniqueVarsAndConsts,LeafDag,DecodedVs),
  once(append(OCs,PIs,DecodedVs)),
  GateCount is LeafCount-1.

generate_leaf_dag(UniqueVarAndConstCount,LeafCount,UniqueVarsAndConsts,
                                                   ETree,StepCounter,OutputSpec):-
  length(Leaves,LeafCount),
  functions_from(Leaves,UniqueVarsAndConsts),
  enumerate_tree_candidates(UniqueVarAndConstCount,LeafCount,Leaves,ETree,O0),
  count_step(StepCounter), %
  trace_step(1000000,StepCounter), %
  OutputSpec=O0.
 
enumerate_tree_candidates(UniqueVarAndConstCount,LeafCount,Leaves,ETree,OutputSpec):-
  N is LeafCount-1,
  length(Nodes,N),
  generate_expression_tree(UniqueVarAndConstCount,ETree,OutputSpec,Leaves,[],Nodes,[]).

generate_expression_tree(_,V,V,[V|Leaves],Leaves)-->[].
generate_expression_tree(NbOfBits,ETree,OutputSpec,Vs1,VsN)-->[_],
  generate_expression_tree(NbOfBits,L,O1,Vs1,Vs2),
  generate_expression_tree(NbOfBits,R,O2,Vs2,VsN),
  {combine_expression_values(NbOfBits,L,R,O1,O2,ETree,OutputSpec)}.

decode_leaf_dag(BooleanExpression,Is,LeafDag,UniqueVars):-
  bitstring_ints_to_vars(BooleanExpression,Is,LeafDag,Us0),
  append(Us0,[],UniqueVars),
  !.
decode_leaf_dag(BooleanExpression,Is,BooleanExpression,Is).
  
% decodes an leaf-dag with variables as bitvector ints 
% to a leaf-dag with logical variables  
bitstring_ints_to_vars(BooleanExpression,Is, LeafDag,UniqueVars):-
  integer(BooleanExpression),
  !,
  comember(BooleanExpression,LeafDag,Is,UniqueVars).
bitstring_ints_to_vars(BooleanExpression,Is, LeafDag,UniqueVars):-
  BooleanExpression=..[Operator,X,Y],
  LeafDag=..[Operator,A,B],
  bitstring_ints_to_vars(X,Is,A,UniqueVars),
  bitstring_ints_to_vars(Y,Is,B,UniqueVars).

% ensures X,Y are members in two list in identical positions  
comember(X,Y,[X|_],[Y|_]).
comember(X,Y,[_|Xs],[_|Ys]):-
  comember(X,Y,Xs,Ys).

% step counter for fast change_arg-based count incrementing
new_step_counter(s(0)).

% get count of backtracking steps
count_step(StepCounter):-arg(1,StepCounter,X),NewX is X+1,change_arg(1,StepCounter,NewX).

% gets total steps
get_step(StepCounter,X):-arg(1,StepCounter,X).

% show total steps and time
trace_step(Freq,s(I)):- 0=:=I mod Freq,!,
  statistics(runtime,[_,T]),
  S is integer((Freq/T)*1000),
  println([steps=I,time=T,steps/s=S]).
trace_step(_,_).

% shows N as a NbOfBits truth table
ptt(UniqueBitstringIntVars,NbOfBits,N):-
  L is 1<<NbOfBits, 
  println([ttvars=UniqueBitstringIntVars,bits/vars=NbOfBits,truthtable:L=N]),
  int2lbits(L,N,Bs),
  foreach(
    nth_member(B,Bs,I0),
    (I is I0-1,int2lbits(NbOfBits,I,Ts),println(Ts=>B))
  ),
  nl.
    