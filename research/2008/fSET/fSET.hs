module FSET where
import Data.List
import Data.Bits
import Data.Array
import Data.Graph
import Random

o x = 2*x+0
i x = 2*x+1

nat2bits = drop_last . to_rbits . succ where
  drop_last bs=genericTake (l-1) bs where
    l=genericLength bs

bits2nat bs = (from_rbits (bs ++ [1]))-1

all_bitstrings = map nat2bits [0..]

data HFS t = U t | S [HFS t] deriving (Show, Eq)

hfs2nat_ _ (U n) = n
hfs2nat_ ulimit (S es) = 
  ulimit + set2nat (map (hfs2nat_ ulimit) es)

set2nat ns = sum (map (2^) ns)

hfs2nat = hfs2nat_ urelement_limit

urelement_limit=0

nat2set n = nat2right_exps n 0 where
  nat2right_exps 0 _ = []
  nat2right_exps n e = add_rexp (n `mod` 2) e 
    (nat2right_exps (n `div` 2) (e+1)) where
      add_rexp 0 _ es = es
      add_rexp 1 e es = (e:es)

nat2hfs_ ulimit n | n<ulimit = U n 
nat2hfs_ ulimit n = 
  S (map (nat2hfs_ ulimit) (nat2set (n-ulimit)))

nat2hfs = nat2hfs_ urelement_limit

iterative_hfs_generator = map nat2hfs [0..]

list_subsets [] = [[]]
list_subsets (x:xs) = 
  [zs|ys<-list_subsets xs,zs<-[ys,(x:ys)]]

hfs_generator = uhfs_from 0 where
  uhfs_from k = union (old_hfs k) (uhfs_from (k+1))
  
  old_hfs k = elements_of (hpow k (U 0))
  elements_of (U _) = []
  elements_of (S hs) = hs
 
  hpow 0 h = h
  hpow k h = hpow (k-1) (S (hsubsets h))

  hsubsets (U n) =  []
  hsubsets (S hs) = (map S (list_subsets hs))

nat2hypergraph = (map nat2set) . nat2set
hypergraph2nat = set2nat . (map set2nat)

hfold f g (U n) = g n
hfold f g (S xs) = f (map (hfold f g) xs)

hsize = hfold f g where
  f xs = 1+(sum xs)
  g _ =1

nfold f g n = nfold_ f g urelement_limit n

nfold_ f g ulimit n | n<ulimit = g n
nfold_ f g ulimit n = 
  f (map (nfold_ f g ulimit) (nat2set n))

nsize = nfold  f g where 
  f xs = 1+(sum xs)
  g _ =1

nsize_alt n = hsize (nat2hfs n)

toNat f = nat2hfs . f . (map  hfs2nat)

toNat1 f i = nat2hfs (f (hfs2nat i))
toNat2 f i j = nat2hfs (f (hfs2nat i) (hfs2nat j))

toHFS f = hfs2nat . f . (map nat2hfs)

toHFS1 f x = hfs2nat (f (nat2hfs x))
toHFS2 f x y = hfs2nat (f (nat2hfs x) (nat2hfs x))

toExps f = set2nat . f . (map nat2set)
fromExps f = nat2set . f . (map set2nat)

setOp f []=[]
setOp f (x:xs) = foldl f x xs

nat_adduction i is = 
  set2nat (union [i] (nat2set is))
  
nat_singleton i = 2^i

nat_intersect = nats_intersect . nat2set 
nats_intersect = toExps (setOp intersect)

nat_union = nats_union . nat2set 
nats_union = toExps (setOp union)

nat_equal i j = if i==j then 1 else 0

hsucc = toNat1 succ
hsum = toNat sum
hproduct = toNat product
hequal = toNat2 nat_equal
hexp2  = toNat1 (2^)

nat_kpair x y = nat_adduction sx ssxy where
  sx = nat_singleton x
  sy = nat_singleton y
  sxy = nat_adduction x sy
  ssxy = nat_singleton sxy

nat_cpair x y = (x+y)*(x+y+1) `div` 2+y

bitmerge_pair (i,j) = 
  set2nat ((evens i) ++ (odds j)) where
    evens x = map (*2) (nat2set x)
    odds y = map succ (evens y)
  
bitmerge_unpair n = (f xs,f ys) where 
  (xs,ys) = partition even (nat2set n)
  f = set2nat . (map (`div` 2))

nat_powset i = set2nat 
  (map set2nat (list_subsets (nat2set i)))

nat_powset_alt i = product 
  (map (\k->1+2^(2^k)) (nat2set i)) 

nat_ordinal 0 = 0
nat_ordinal n = 
  set2nat (map nat_ordinal [0..(n-1)])

hfs_ordinal = nat2hfs . nat_ordinal

nat_choice_fun i =  set2nat xs where 
  es = nat2set i
  hs = map (head . nat2set) es
  xs = zipWith (curry bitmerge_pair) es hs

nat2memb = nat2pairs with_memb
nat2contains = nat2pairs with_contains

with_memb a x = (x,a)
with_contains a x = (a,x)

nat2member_dag = nat2dag_ nat2memb 

nat2contains_dag = nat2dag_ nat2contains   

nat2dag_ f n = buildG (0,l) es where 
  es=reverse (f n)
  l=foldl max 0 (nat2parts n)

to_dag n = (buildG (0,l) 
  (map (remap m) (nat2contains n))) where  
    is = [0..l]
    ns =  reverse (nat2parts n)
    l = (genericLength ns)-1
    m= (zip ns is)
    remap m (f,t) =  (lf,lt) where 
      (Just lf)=(lookup f m) 
      (Just lt)=(lookup t m)

to_ddag = transposeG . to_dag

from_dag g = 
  compute_decoration g (fst (bounds g))

compute_decoration g v = 
  compute_decorations g (g!v) where
    compute_decorations _ [] = 0
    compute_decorations g es =
      sum (map ((2^) . (compute_decoration g)) es)

from_ddag g = 
  compute_decoration g (snd (bounds g))

intensional_dual_of = from_ddag . to_ddag

self_idual n = n==intensional_dual_of n

self_iduals from to = 
  filter self_idual [from..to]  

nat2digraph n = map bitmerge_unpair (nat2set n)
digraph2nat ps = set2nat (map bitmerge_pair ps)

-- from decimals to binary as list of bits
to_rbits n = to_base 2 n

-- from bits to decimals
from_rbits bs = from_base 2 bs

-- conversion to base n, as list of digits
to_base base n = d : 
  (if q==0 then [] else (to_base base q)) where
    (q,d) = quotRem n base

-- conversion from any base to decimal 
from_base base [] = 0
from_base base (x:xs) = x+base*(from_base base xs)

setShow n = sShow urelement_limit n

sShow 1 0 = "{}"
sShow ulimit n | n<ulimit = show n
sShow ulimit n = "{"++ 
  foldl (++) "" 
    (intersperse "," (map (sShow ulimit) (nat2set (n-ulimit)))) 
  ++"}"

nat2pairs withF n  = (sort . nub)  (nat2ps withF n)

nat2ps withF 0 = []
nat2ps withF from = 
  ((n2rel ns) ++ (ns2rel ns)) where
    f = withF from
    n2rel = map f
    ns2rel = concatMap (nat2ps withF)
    ns=nat2set from 

nat2parts = sort . nub . nat2repeated where
  nat2repeated 0 = [0]
  nat2repeated from = from : (nat2more ns) where
    nat2more = concatMap nat2repeated
    ns=nat2set from 

mprint f = (mapM_ print) . (map f)

