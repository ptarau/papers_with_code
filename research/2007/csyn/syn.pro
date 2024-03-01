:-[csyn].
:-[funs].
:-[eval].

:-[tools].
:-[ttbits].

:-[tests].

/*
:-[nsyn].
:-[nif].
:-[rewrite].
% :-[dc].
*/

syn(E):-synthesize_circuit(E).

syn16:-synthesize_2_arg_boolean_operators.
