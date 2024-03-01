% catalan pbjects / binary trees
cat(N,T):-gen(N,[v/0,a/2],T).

% catalan generators

cat_funs([v/0,a/2]).
 
cat_ext(Size,Es):-cat_funs(Fs),ext_test(Size,Fs,Es).

cat_all(Size,T):-cat_funs(Fs),gen_terms(Size,Fs,T).

cat_gens(Size,T):-cat_funs(Fs),gen_terms(Size,Fs,T).

cat_gen(Size,T):-cat_funs(Fs),gen_term(Size,Fs,T).

% stats

cc(N):-ncounts(N,cat(_,_)).
bc(N):-ntimes(N,cat(_,_)).
sc(N):-nshow(N,cat(_,_)). 
pc(N):-npp(N,cat(_,_)).

cce(N):-ncounts(N,cat_ext(_,_)).
bce(N):-ntimes(N,cat_ext(_,_)).
sce(N):-nshow(N,cat_ext(_,_)). 

ccx(N):-ncounts(N,cat_all(_,_)).
bcx(N):-ntimes(N,cat_all(_,_)).
scx(N):-nshow(N,cat_all(_,_)). 

ccg(N):-ncounts(N,cat_gen(_,_)).
bcg(N):-ntimes(N,cat_gen(_,_)).
scg(N):-nshow(N,cat_gen(_,_)). 
pcg(N):-npp(N,cat_gen(_,_)).

% functor counts

fc1(N):-sct(N,cat(_,_)).
fc2(N):-sct(N,cat_all(_,_)).
fc3(N):-sct(N,cat_gen(_,_)).
