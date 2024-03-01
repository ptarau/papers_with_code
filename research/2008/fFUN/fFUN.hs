module FFUN where
import Data.List
import Data.Bits
import Data.Array
import Data.Graph
import Random

double n = 2*n
half n = n `div` 2
exp2 n = 2^n

data T a = A a | F [T a] deriving (Eq,Ord,Read,Show)

unrank_ ulimit _ n | (n<ulimit) && (n>=0) = A n
unrank_ ulimit f n | n >=ulimit = 
  (F (map (unrank_ ulimit f) (f  (n-ulimit))))

default_ulimit = 0

unrank = unrank_ default_ulimit

rank_ ulimit _ (A n) | (n<ulimit) && (n>=0) = n
rank_ ulimit g (F ts) = 
  ulimit+(g (map (rank_ ulimit g) ts))

rank = rank_ default_ulimit

hfs2nat = rank set2nat

set2nat ns = sum (map exp2 ns)

nat2set n = nat2exps n 0 where
  nat2exps 0 _ = []
  nat2exps n x = 
    if (even n) then xs else (x:xs) where
      xs=nat2exps (half n) (succ x)

nat2hfs = unrank nat2set

iterative_hfs_generator=map nat2hfs [0..]

nat_cpair x y = (x+y)*(x+y+1) `div` 2+y

pepis_J x y  = pred ((exp2 x)*(succ (double y)))

pepis_K n = two_s (succ n)

pepis_L n = half (pred (no_two_s (succ n)))
 
two_s n | even n = succ (two_s (half n))
two_s _ = 0

no_two_s n = n `div` (exp2 (two_s n))

haskell2pepis (x,y) = pepis_J x y
pepis2haskell n = (pepis_K n,pepis_L n)

bitmerge_pair (i,j) = 
  set2nat ((evens i) ++ (odds j)) where
    evens x = map double (nat2set x)
    odds y = map succ (evens y)
  
bitmerge_unpair n = (f xs,f ys) where 
  (xs,ys) = partition even (nat2set n)
  f = set2nat . (map half)

to_tuple k n = map from_rbits (
    transpose (
      map (to_maxbits k) (
        to_base (exp2 k) n
      )
    )
  )

from_tuple ns = from_base (exp2 k) (
    map from_rbits (
      transpose (
        map (to_maxbits l) ns
      )
    )
  ) where 
      k=genericLength ns
      l=max_bitcount ns

ftuple2nat [] = 0
ftuple2nat ns = haskell2pepis (pred k,t) where
  k=genericLength ns 
  t=from_tuple ns

nat2ftuple 0 = []
nat2ftuple kf = to_tuple (succ k) f where 
  (k,f)=pepis2haskell kf

fun2set ns = 
  map pred (tail (scanl (+) 0 (map succ ns)))

set2fun ns = map pred (genericTake l ys) where 
  l=genericLength ns
  xs =(map succ ns)
  ys=(zipWith (-) (xs++[0]) (0:xs))

nat2fun = set2fun . nat2set

fun2nat = set2nat . fun2set

bits2rle [] = []
bits2rle [_] = [0]
bits2rle (x:y:xs) | x==y = (c+1):cs where 
  (c:cs)=bits2rle (y:xs)
bits2rle (_:xs) = 0:(bits2rle xs)

rle2bits [] = []
rle2bits (n:ns) = 
  (genericReplicate (n+1) b) ++ xs where 
    xs=rle2bits ns
    b=if []==xs then 1 else 1-(head xs)

nat2rle = bits2rle . to_rbits0

rle2nat = from_rbits . rle2bits

to_rbits0 0 = []
to_rbits0 n = to_rbits n


nat2hff = unrank nat2fun
nat2hff1 = unrank nat2ftuple
nat2hff2 =  unrank nat2rle

hff2nat = rank fun2nat
hff2nat1 = rank ftuple2nat
hff2nat2 = rank rle2nat

-- factoradics of n, right to left
fr 0 = [0]
fr n = f 1 n where
   f _ 0 = []
   f j k = (k `mod` j) : 
           (f (j+1) (k `div` j))

fl = reverse . fr

rf ns = sum (zipWith (*) ns factorials) where
  factorials=scanl (*) 1 [1..]

lf = rf . reverse

perm2nth ps = (l,lf ls) where 
  ls=perm2lehmer ps
  l=genericLength ls

perm2lehmer [] = []
perm2lehmer (i:is) = l:(perm2lehmer is) where
  l=genericLength [j|j<-is,j<i]  

-- generates n-th permutation of given size
nth2perm (size,n) = 
  apply_lehmer2perm (zs++xs) [0..size-1] where 
    xs=fl n
    l=genericLength xs
    k=size-l
    zs=genericReplicate k 0

-- converts Lehmer code to permutation   
lehmer2perm xs = apply_lehmer2perm xs is where 
  is=[0..(genericLength xs)-1]

-- extracts permutation from factoradic "digit" list    
apply_lehmer2perm [] [] = []
apply_lehmer2perm (n:ns) ps@(x:xs) = 
   y : (apply_lehmer2perm ns ys) where
   (y,ys) = pick n ps

pick i xs = (x,ys++zs) where 
  (ys,(x:zs)) = genericSplitAt i xs

-- fast computation of the sum of all factorials up to n!
sf n = rf (genericReplicate n 1)

sfs = map sf [0..]

to_sf n = (k,n-m) where 
  k=pred (head [x|x<-[0..],sf x>n])
  m=sf k

nat2perm 0 = []
nat2perm n = nth2perm (to_sf n)

perm2nat ps = (sf l)+k where 
  (l,k) = perm2nth ps

perms = map nat2perm [0..]

nat2hfp = unrank nat2perm
hfp2nat = rank perm2nat

setShow = (gshow "{" "," "}") . nat2hfs
funShow = (gshow "(" " " ")") . nat2hff
funShow1 = (gshow "(" " " ")") . nat2hff1
funShow2 = (gshow "(" " " ")") . nat2hff2
permShow = (gshow "(" " " ")") . nat2hfp

gshow _ _ _ (A n) = show n
gshow l _ r (F []) = 
  -- empty function shown as 0 rather than ()
  if default_ulimit > 1 then "0" else l++r
gshow l c r (F ns) = l++ 
  foldl (++) "" 
    (intersperse c (map (gshow l c r) ns)) 
  ++r  

bitcount n = head [x|x<-[1..],(exp2 x)>n]
max_bitcount ns = foldl max 0 (map bitcount ns)

-- from decimals to binary as list of bits
to_rbits n = to_base 2 n

-- from bits to decimals
from_rbits bs = from_base 2 bs

-- to binary, padded with 0s, up to maxbits
to_maxbits maxbits n = 
  bs ++ (genericTake (maxbits-l)) (repeat 0) where 
    bs=to_base 2 n
    l=genericLength bs

-- conversion to base n, as list of digits
to_base base n = d : 
  (if q==0 then [] else (to_base base q)) where
    (q,d) = quotRem n base

-- conversion from any base to decimal 
from_base base [] = 0
from_base base (x:xs) = x+base*(from_base base xs)


mprint f = (mapM_ print) . (map f)

stest = mprint setShow [0..88]
ftest = mprint funShow [0..88]
ftest1 = mprint funShow1 [0..88]
ftest2 = mprint funShow2 [0..88]

{-
randomList seed max = randomRs (0,max) (mkStdGen seed)

smalls n = genericTake n (randomList 13 (2^8))

-- issue with type here in 6.8.3
ptest = permShow (ran 42)



random_nats k = randomList k (2^2^8)

rans k n = genericTake n (random_nats k)

ran k = head (random_nats k)

rantest seed  = mapM_ print [f,f1,f2] where
  n = ran seed 
  f = nat2hff n
  f1 = nat2hff1 n
  f2 = nat2hff2 n
  p = nat2hfp n
 
srantest seed  = print (nat2hfs (ran seed))

-}

btest = is_bij_up_to (2^default_ulimit)

is_bij_up_to n = all==trimmed where
  all=map nat2hfs [0..n-1]
  trimmed = nub all
  

