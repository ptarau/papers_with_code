module MPrimes where
import Data.List
import Data.Bits

import Graphics.Gnuplot.Simple

data Iso a b = Iso (a->b) (b->a)

from (Iso f _) = f
to (Iso _ g) = g

compose :: Iso a b -> Iso b c -> Iso a c
compose (Iso f g) (Iso f' g') = Iso (f' . f) (g . g')

itself = Iso id id

invert (Iso f g) = Iso g f

type N = Integer
type Hub = [N]

type Encoder a = Iso a Hub

as :: Encoder a -> Encoder b -> b -> a
as that this x = g x where 
   Iso _ g = compose that (invert this)

borrow_from :: Encoder a -> (a -> a -> a) -> 
               Encoder b -> (b -> b -> b)
borrow_from lender op borrower x y = as borrower lender
   (op (as lender borrower x) (as lender borrower y))

list :: Encoder [N]
list = itself

set2list :: [N] -> [N]
set2list xs = shift_tail pred (mset2list xs) where
  shift_tail _ [] = []
  shift_tail f (x:xs) = x:(map f xs)

list2set :: [N] -> [N]  
list2set = (map pred) . list2mset . (map succ)

set :: Encoder [N]
set = Iso set2list list2set

nat_set = Iso nat2set set2nat 

nat2set :: N->[N]
nat2set n | n>=0 = nat2exps n 0 where
  nat2exps 0 _ = []
  nat2exps n x = if (even n) then xs else (x:xs) where
    xs=nat2exps (n `div` 2) (succ x)

set2nat :: [N]->N
set2nat ns = sum (map (2^) ns)

nat :: Encoder N
nat = compose nat_set set

nat2pmset :: N->[N]
nat2pmset 1 = []
nat2pmset n = to_prime_positions n

pmset2nat :: [N]->N
pmset2nat [] = 1
pmset2nat ns = 
  product (map (from_pos_in primes . pred) ns)

pmset :: Encoder [N]
pmset = compose (Iso pmset2nat nat2pmset) nat

mset2list :: [N]->[N]
mset2list = to_diffs . sort
to_diffs xs = zipWith (-) (xs) (0:xs)

list2mset :: [N]->[N]
list2mset ns = tail (scanl (+) 0 ns) 

mset0 :: Encoder [N]
mset0 = Iso mset2list list2mset

nat2mset1 :: N->[N]
nat2mset1 n = map succ (as mset0 nat (pred n))

mset2nat1 :: [N]->N
mset2nat1 ns = succ (as nat mset0 (map pred ns)) 

mset :: Encoder [N]
mset = compose (Iso mset2nat1 nat2mset1) nat

mprod = borrow_from mset (++) nat

mprod_alt n m = 
   as nat mset ((as mset nat n) ++ (as mset nat m))

mproduct ns = foldl mprod 1 ns

pmprod n m = 
   as nat pmset ((as pmset nat n) ++ (as pmset nat m))

mexp n 1 = n
mexp n k = mprod n (mexp n (k-1))

mgcd :: N -> N -> N
mgcd = borrow_from mset msetInter nat

mlcm :: N -> N -> N
mlcm = borrow_from mset msetUnion nat

mdivisible :: N->N->Bool
mdivisible n m = mgcd n m==m

mdiv :: N -> N -> N
mdiv = borrow_from mset msetDif nat
  
mexactdiv :: N -> N -> N
mexactdiv n m | mdivisible n m = mdiv n m

is_mprime p | p >1 = 1==length (as mset nat p)

alt_is_mprime p | p>1 = 
  []==[n|n<-[2..p-1],p `mdivisible` n]

mprimes = filter is_mprime [2..]

mprimes' = map (\x->2^x+1) [0..]

is_mprime' p | p>1 = p == last 
  (takeWhile (\x->x<=p) mprimes') 

rad n = product (nub (to_primes n))

pfactors n = nub (as pmset nat n)
mfactors n = nub (as mset nat n)

prad n =  as nat pmset (pfactors n)

mrad n =  as nat mset (mfactors n)

nats2goedel ns =  product xs where
  xs=zipWith (^) primes ns

goedel2nats n = combine ds xs where
  pss=group (to_primes n)
  ps=map head pss
  xs=map genericLength pss
  ds=as list set (map pi' ps)
  
  combine [] [] = []
  combine (b:bs) (x:xs) = 
    replicate (fromIntegral b) 0 ++ x:(combine bs xs)

pi' p | is_prime p= to_pos_in primes p 

goedel :: Encoder [N]
goedel = compose (Iso nats2g g2nats) nat

nats2g [] = 0
nats2g ns = pred (nats2goedel (z:ns)) where
  z=countZeros (reverse ns)

g2nats 0 = []  
g2nats n = ns ++ (replicate (fromIntegral z) 0) where 
  (z:ns)=goedel2nats (succ n)
    
countZeros (0:ns) = 1+countZeros ns
countZeros _ = 0

goedel' :: Encoder [N]
goedel' = compose (Iso nats2gnat gnat2nats) nat

nats2gnat = pmset2nat . (as mset list)

gnat2nats = (as list mset) . nat2pmset

invo_m2m n = (as nat list . reverse . as list nat) n

invo_p2p n = as nat pmset qs where
  ps=as pmset nat n
  ns=as list pmset ps
  rs=reverse ns
  qs=as pmset list rs
  

auto_m2p 0 = 0   
auto_m2p n = as nat pmset (as mset nat n) 

auto_p2m 0 = 0
auto_p2m n = as nat mset (as pmset nat n)

lt_mp n = length [x|x<-[0..n],auto_m2p x < auto_p2m x]
eq_mp n = length [x|x<-[0..n],auto_m2p x == auto_p2m x]
gt_mp n = length [x|x<-[0..n],auto_m2p x > auto_p2m x]

auto_m2g 0 = 0   
auto_m2g n = as nat goedel (as list nat n) 

auto_g2m 0 = 0
auto_g2m n = as nat list (as goedel nat n)

auto_p2g 0 = 0   
auto_p2g n = as nat goedel (as goedel' nat n) 

auto_g2p 0 = 0
auto_g2p n = as nat goedel' (as goedel nat n)

type NxN = (N,N)

bitpair ::  NxN -> N
bitpair (i,j) = 
  set2nat ((evens i) ++ (odds j)) where
    evens x = map (2*) (nat2set x)
    odds y = map succ (evens y)

bitunpair :: N->NxN  
bitunpair n = (f xs,f ys) where 
  (xs,ys) = partition even (nat2set n)
  f = set2nat . (map (`div` 2))

nat2 :: Encoder NxN
nat2 = compose (Iso bitpair bitunpair) nat

pair2unord_pair (x,y) = list2set [x,y]
unord_pair2pair [a,b] = (x,y) where 
  [x,y]=set2list [a,b]   

unord_unpair = pair2unord_pair . bitunpair
unord_pair = bitpair . unord_pair2pair

set2 :: Encoder [N]
set2 = compose (Iso unord_pair2pair pair2unord_pair) nat2

pair2mset_pair (x,y) = (a,b) where 
  [a,b]=list2mset [x,y]
mset_unpair2pair (a,b) = (x,y) where 
  [x,y]=mset2list [a,b]

mset_unpair = pair2mset_pair . bitunpair
mset_pair = bitpair . mset_unpair2pair

mset2 :: Encoder NxN
mset2 = 
  compose (Iso mset_unpair2pair pair2mset_pair) nat2

bitlift :: N -> N
bitlift x = bitpair (x,0)

bitlift' :: N -> N
bitlift' = (from_base 4) . (to_base 2)

bitclip :: N -> N
bitclip = fst . bitunpair

bitclip' :: N -> N
bitclip' = (from_base 2) . 
   (map (`div` 2)) . (to_base 4) . (*2)

bitpair' (x,y) = (bitpair (x,0))   +   (bitpair(0,y))
xbitpair (x,y) = (bitpair (x,0)) `xor` (bitpair (0,y))
obitpair (x,y) = (bitpair (x,0))  .|.  (bitpair (0,y))

bitpair'' (x,y) = mset_pair (min x y,x+y) 

bitpair''' (x,y) = unord_pair [min x y,x+y+1]

mset_pair' (a,b) = 
  bitpair (min a b, (max a b) - (min a b)) 

mset_pair'' (a,b) = 
  unord_pair [min a b, (max a b)+1]

unord_pair' [a,b] = 
  bitpair (min a b, (max a b) - (min a b) -1) 

unord_pair'' [a,b] = 
  mset_pair (min a b, (max a b)-1)

ppair :: (NxN -> N) -> NxN -> N
ppair pairingf (p1,p2) | is_prime p1 && is_prime p2 = 
  from_pos_in ps 
    (pairingf (to_pos_in ps p1,to_pos_in ps p2)) where 
       ps = primes
       
punpair :: (N -> NxN) -> N -> NxN
punpair unpairingf p | is_prime p = 
  (from_pos_in ps n1,from_pos_in ps n2) where 
    ps=primes
    (n1,n2)=unpairingf (to_pos_in ps p)

hyper_primes u = 
  [n|n<-primes, all_are_primes (uparts u n)] where
     all_are_primes ns = and (map is_prime ns)
  
uparts u = sort . nub . tail . (split_with u) where
    split_with _ 0 = []
    split_with _ 1 = []
    split_with u n = 
      n:(split_with u n0)++(split_with u n1) where
        (n0,n1)=u n  

hyper_mprimes :: (N -> NxN) -> [N]
hyper_mprimes u = 
  [n|n<-mprimes', all_are_mprimes (uparts u n)] where
     all_are_mprimes ns = and (map is_mprime' ns)

primes :: [N]
primes = 2 : filter is_prime [3,5..]

is_prime :: N -> Bool
is_prime p = [p]==to_primes p

to_primes n | n>1 = to_factors n p ps where 
  (p:ps) = primes

to_factors n p ps | p*p > n = [n]
to_factors n p ps | 0==n `mod` p = 
   p : to_factors (n `div` p)  p ps 
to_factors n p ps@(hd:tl) = to_factors n hd tl

to_prime_positions n=
  map (succ . (to_pos_in (h:ps))) qs where
    (h:ps)=genericTake n primes
    qs=to_factors n h ps
   
to_pos_in xs x = fromIntegral i where 
   Just i=elemIndex x xs

from_pos_in xs n = xs !! (fromIntegral n)   

msetInter, msetDif, msetSymDif, msetUnion :: 
  (Ord a) => [a] -> [a] -> [a]
  
msetInter xs ys = sort (msetInter' xs ys) where
  msetInter' [] _ = []
  msetInter' _ [] = []
  msetInter' (x:xs) (y:ys) | x==y = 
    (x:zs) where zs=msetInter' xs ys
  msetInter' (x:xs) (y:ys) | x<y = msetInter' xs (y:ys)
  msetInter' (x:xs) (y:ys) | x>y = msetInter' (x:xs) ys

msetDif xs ys = sort (msetDif' xs ys) where
  msetDif' [] _ = []
  msetDif' xs [] = xs
  msetDif' (x:xs) (y:ys) | x==y = zs where 
    zs=msetDif' xs ys
  msetDif' (x:xs) (y:ys) | x<y = (x:zs) where 
    zs=msetDif' xs (y:ys)
  msetDif' (x:xs) (y:ys) | x>y = zs where 
    zs=msetDif' (x:xs) ys

msetSymDif xs ys = 
  sort ((msetDif xs ys) ++ (msetDif ys xs))

msetUnion xs ys = sort ((msetDif xs ys) ++ 
  (msetInter xs ys) ++ (msetDif ys xs))

to_base:: N->N->[N]
to_base base n = d : 
   (if q==0 then [] else (to_base base q)) where
       (q,d) = quotRem n base

from_base::N->[N]->N
from_base base [] = 0
from_base base (x:xs) | x>=0 && x<base = 
  x+base*(from_base base xs)

-- misc explorations

decomp a b = (a `div` d,d,b `div` d) where d=gcd a b  

arith_pair (x,y) = bitpair (d-1,(bitpair (a',b')))-2 where 
  a=x+2
  b=y+2
  d=gcd a b
  a'=a `div` d
  b'=b `div` d
 
arith_unpair n = (a-2,b-2) where
  n'=n+2
  (z,d)=bitunpair n'
  (a',b')=bitunpair z
  d'=d+1
  a=a'*d'
  b=b'*d'
    
    
plotfun f m = plotList 
  [Title ""] 
  (map f [0..2^m-1])
      

