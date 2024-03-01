Exact Circuit Synthetiser in Prolog
===================================

On a Windows PC type:

go <library>

(for instance

go nand
go less
go leq1
go impl
go and_xor
...
).

Library definitions are the files starting with lib_. They can be 
easily modified to create new ones.

At the prolog prompt, type something like:

?- syn(A*B=>B*C). % to synthesize from boolean expression

?-syn(3:29). % to synthetise from 3 bit truth table 29
             % seen as the 2^3 bit vector

The main file is syn.pro the "toplevel" algorithm is
in csyn.pro. Various libraries symply include syn.pro
and add extend it with their definitions - that's why
go.bat calls them as argument to the Prolog system.

The code is portable, except for some step counting functions 
that use BinProlog and Jinni specifics like change_arg and if_any.
For a quick port to another Prolog just comment that out in csyn.pro.

This version supports at most 4 variables as it only uses
16 bits out of BinProlog's 29 bit integers. In a Prolog
with arbitrary length ints this should work with more,
provided that the problem is tractable computationaly.

If you want to see a 3D representation of the synthetised
circuits as Leaf DAGs, please download an evaluation copy from

http://binnetcorp.com/Jinni

as well as Java3D and try out syn3d(Expr) and type

jgo.bat instead of go.bat in the previous examples.



