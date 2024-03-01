% motzkin generators

% Motzkin trees

mot_funs([v/0,l/1,a/2]).

mot(N,T):-mot_funs(CFs),gen(N,CFs,T).

mot_ext(Size,Es):-mot_funs(CFs),ext_test(Size,CFs,Es).
  
mot_all(Size,T):-mot_funs(CFs),gen_terms(Size,CFs,T).

mot_gens(Size,T):-mot_funs(CFs),gen_term(Size,CFs,T).

mot_gen(Size,T):-mot_funs(CFs),gen_term(Size,CFs,T).

cm(N):-ncounts(N,mot(_,_)).
bm(N):-ntimes(N,mot(_,_)).
sm(N):-nshow(N,mot(_,_)). 
pm(N):-npp(N,mot(_,_)).

cme(N):-ncounts(N,mot_ext(_,_)).
bme(N):-ntimes(N,mot_ext(_,_)).
sme(N):-nshow(N,mot_ext(_,_)). 


cmx(N):-ncounts(N,mot_all(_,_)).
bmx(N):-ntimes(N,mot_all(_,_)).
smx(N):-nshow(N,mot_all(_,_)). 

cmg(N):-ncounts(N,mot_gen(_,_)).
bmg(N):-ntimes(N,mot_gen(_,_)).
smg(N):-nshow(N,mot_gen(_,_)). 
pmg(N):-npp(N,mot_gen(_,_)). 

fm1(N):-nct(N,mot(_,_)).
fm2(N):-nct(N,mot_all(_,_)).
fm3(N):-nct(N,mot_gen(_,_)).
