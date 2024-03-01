% SK combinators

sk_funs([s/0,k/0,a/2]).

sk(N,T):-sk_funs(CFs),gen(N,CFs,T).

sk_ext(Size,Es):-sk_funs(CFs),ext_test(Size,CFs,Es).
  
sk_all(Size,T):-sk_funs(CFs),gen_terms(Size,CFs,T).

sk_gens(Size,T):-sk_funs(CFs),gen_term(Size,CFs,T).

sk_gen(Size,T):-sk_funs(CFs),gen_term(Size,CFs,T).

csk(N):-ncounts(N,sk(_,_)).
bsk(N):-ntimes(N,sk(_,_)).
ssk(N):-nshow(N,sk(_,_)). 
psk(N):-npp(N,sk(_,_)).

cske(N):-ncounts(N,sk_ext(_,_)).
bske(N):-ntimes(N,sk_ext(_,_)).
sske(N):-nshow(N,sk_ext(_,_)). 


cskx(N):-ncounts(N,sk_all(_,_)).
bskx(N):-ntimes(N,sk_all(_,_)).
sskx(N):-nshow(N,sk_all(_,_)). 

cskg(N):-ncounts(N,sk_gen(_,_)).
bskg(N):-ntimes(N,sk_gen(_,_)).
sskg(N):-nshow(N,sk_gen(_,_)). 
pskg(N):-npp(N,sk_gen(_,_)). 

fsk1(N):-nct(N,sk(_,_)).
fsk2(N):-nct(N,sk_all(_,_)).
fsk3(N):-nct(N,sk_gen(_,_)).
