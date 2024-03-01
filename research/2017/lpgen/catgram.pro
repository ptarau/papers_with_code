% basic categorial grammar

gram_funs([t/0,e/0,left_arrow/2,right_arrow/2]).

gram(N,T):-gram_funs(CFs),gen(N,CFs,T).

gram_ext(Size,Es):-gram_funs(CFs),ext_test(Size,CFs,Es).
  
gram_all(Size,T):-gram_funs(CFs),gen_terms(Size,CFs,T).

gram_gens(Size,T):-gram_funs(CFs),gen_term(Size,CFs,T).

gram_gen(Size,T):-gram_funs(CFs),gen_term(Size,CFs,T).

cgr(N):-ncounts(N,gram(_,_)).
bgr(N):-ntimes(N,gram(_,_)).
sgr(N):-nshow(N,gram(_,_)). 
pgr(N):-npp(N,gram(_,_)).

cgre(N):-ncounts(N,gram_ext(_,_)).
bgre(N):-ntimes(N,gram_ext(_,_)).
sgre(N):-nshow(N,gram_ext(_,_)). 


cgrx(N):-ncounts(N,gram_all(_,_)).
bgrx(N):-ntimes(N,gram_all(_,_)).
sgrx(N):-nshow(N,gram_all(_,_)). 

cgrg(N):-ncounts(N,gram_gen(_,_)).
bgrg(N):-ntimes(N,gram_gen(_,_)).
sgrg(N):-nshow(N,gram_gen(_,_)). 
pgrg(N):-npp(N,gram_gen(_,_)). 

fgr1(N):-nct(N,gram(_,_)).
fgr2(N):-nct(N,gram_all(_,_)).
fgr3(N):-nct(N,gram_gen(_,_)).
