module MPrimes where
import Data.List
import Data.Bits

import Graphics.Gnuplot.Simple

nat2pmset 1 = []
nat2pmset n = to_prime_positions n

pmset2nat [] = 1
pmset2nat ns = 
  product (map (from_pos_in primes . pred) ns)

pmset :: Encoder [N]
pmset = compose (Iso pmset2nat nat2pmset) nat

mset2list = to_diffs . sort
to_diffs xs = zipWith (-) (xs) (0:xs)

list2mset ns = tail (scanl (+) 0 ns) 

mset0 :: Encoder [N]
mset0 = Iso mset2list list2mset

nat2mset1 n=map succ (as mset0 nat (pred n))
mset2nat1 ns=succ (as nat mset0 (map pred ns)) 

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

is_mprime' p | p>1 = p==
  last (takeWhile (\x->x<=p) mprimes') 

rad n = product (nub (to_primes n))

pfactors n = nub (as pmset nat n)
mfactors n = nub (as mset nat n)

prad n =  as nat pmset (pfactors n)

mrad n =  as nat mset (mfactors n)

rgcd 1 = 7
rgcd n | n>1 = n' + (gcd n n') where  n'=rgcd (pred n)

dgcd n = (rgcd (succ n')) - (rgcd n') where n'=succ n

rlcm 1 = 1
rlcm n | n>1 = n' + (lcm n n') where  n'=rlcm (pred n)

dlcm n = 
  pred ((rlcm (succ n')) `div` (rlcm n')) where n'=succ n

plcd n = (tail . sort . nub . (map dgcd)) [0..n] 

plcm n = (tail . sort . nub . (map dlcm)) [0..n] 

rmlcm 1 = 1
rmlcm n | n>1 = n' + (mlcm n n') where  n'=rmlcm (pred n)

dmlcm n = 
  pred ((rmlcm (succ n')) `mdiv` (rmlcm n')) where n'=succ n

mplcm n = (tail . sort . nub . (map dmlcm)) [2..n] 

rlcm' n = scanl  (\x y->x+lcm x y) 1 [2..n] 
plcm' n = tail (sort (nub ns')) where
 ns=rlcm' n
 ns'=3:(zipWith (\x y->x `div` y-1) (tail ns) ns) 

primesTo n = tail (sort (nub (take n (3:f 2 1 3)))) where
  f n m m' = (m' `div` m-1) : f (n+1) m' (m' + lcm n m') 

auto_m2p 0 = 0   
auto_m2p n = as nat pmset (as mset nat n) 

auto_p2m 0 = 0
auto_p2m n = as nat mset (as pmset nat n)

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
set2 = 
  compose (Iso unord_pair2pair pair2unord_pair) nat2

pair2mset_pair (x,y) = (a,b) where 
  [a,b]=list2mset [x,y]
mset_unpair2pair (a,b) = (x,y) where 
  [x,y]=mset2list [a,b]

mset_unpair = pair2mset_pair . bitunpair
mset_pair = bitpair . mset_unpair2pair

mset2 :: Encoder NxN
mset2 = 
  compose (Iso mset_unpair2pair pair2mset_pair) nat2

bitlift x = bitpair (x,0)
bitlift' = (from_base 4) . (to_base 2)

bitclip = fst . bitunpair
bitclip' = (from_base 2) . 
   (map (`div` 2)) . (to_base 4) . (*2)

bitpair' (x,y) = (bitpair (x,0))   +   (bitpair(0,y))
xbitpair (x,y) = (bitpair (x,0)) `xor` (bitpair (0,y))
obitpair (x,y) = (bitpair (x,0))  .|.  (bitpair (0,y))

pair_product (x,y) = a+b where
  x'=bitpair (x,0)
  y'=bitpair (0,y)
  ab=x'*y'
  (a,b)=bitunpair ab

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

ppair :: ((N, N) -> N) -> (N, N) -> N
ppair pairingf (p1,p2) | is_prime p1 && is_prime p2 = 
  from_pos_in ps 
    (pairingf (to_pos_in ps p1,to_pos_in ps p2)) where 
       ps = primes
       
punpair :: (N -> (N, N)) -> N -> (N, N)
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

hyper_mprimes u = 
  [n|n<-mprimes', all_are_mprimes (uparts u n)] where
     all_are_mprimes ns = and (map is_mprime' ns)

data Iso a b = Iso (a->b) (b->a)

from (Iso f _) = f
to (Iso _ g) = g

compose :: Iso a b -> Iso b c -> Iso a c
compose (Iso f g) (Iso f' g') = Iso (f' . f) (g . g')
itself = Iso id id
invert (Iso f g) = Iso g f

type N = Integer
type Root = [N]

type Encoder a = Iso a Root

as :: Encoder a -> Encoder b -> b -> a
as that this x = g x where 
   Iso _ g = compose that (invert this)

borrow_from :: Encoder a -> (a -> a -> a) -> 
               Encoder b -> (b -> b -> b)
borrow_from lender op borrower x y = as borrower lender
   (op (as lender borrower x) (as lender borrower y))

list :: Encoder [N]
list = itself

primes = 2 : filter is_prime [3,5..]

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

msetInter xs ys = sort (msetInter' xs ys)

msetInter' [] _ = []
msetInter' _ [] = []
msetInter' (x:xs) (y:ys) | x==y = 
  (x:zs) where zs=msetInter' xs ys
msetInter' (x:xs) (y:ys) | x<y = msetInter' xs (y:ys)
msetInter' (x:xs) (y:ys) | x>y = msetInter' (x:xs) ys

msetDif xs ys = sort (msetDif' xs ys)

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

set2list xs = shift_tail pred (mset2list xs) where
  shift_tail _ [] = []
  shift_tail f (x:xs) = x:(map f xs)
  
list2set = (map pred) . list2mset . (map succ)

set :: Encoder [N]
set = Iso set2list list2set

nat_set = Iso nat2set set2nat 

nat2set n | n>=0 = nat2exps n 0 where
  nat2exps 0 _ = []
  nat2exps n x = if (even n) then xs else (x:xs) where
    xs=nat2exps (n `div` 2) (succ x)

set2nat ns = sum (map (2^) ns)

nat :: Encoder N
nat = compose nat_set set

to_base base n = d : 
   (if q==0 then [] else (to_base base q)) where
       (q,d) = quotRem n base

from_base base [] = 0
from_base base (x:xs) | x>=0 && x<base = 
  x+base*(from_base base xs)

-- misc explorations

-- does Wilson's theorem hold for emulated primes?

fact 0 = 1
fact n = n * (fact (pred n))

is_wilson n | n>1 = gcd (succ (fact n')) n==n where
  n'=pred n
wilson n = is_prime n == is_wilson n 

mfact 0 = 0
mfact n = mprod n (mfact (pred n))

is_mwilson n | n>1 = mgcd (succ (mfact (pred n))) n==n

mwilson n = is_mprime n == is_mwilson n 

-- not interesting, not primes
is_pwilson n | n>1 = mgcd (succ (rad (pred n))) n==n

-- No, it does not!
-- it involves addition - meaningless for mprod ...

-- *MPrimes> map mwilson [2..8]
--[True,True,False,True,True,True,False]
 
 -- rad(n) : A007947 - largest square free divisor --
 -- rad == prad

 


--mrad' n =  mproduct (mfactors n)

plotf f k m = plotList [] (map f [2^k..2^m-1])

radf = plotf rad 1 7
mradf = plotf mrad 1 7





{-
map set of sq free primes to sq free primes

compare: rad(n) with pprad
    
-}  

fn n=product (map fn [0..n-1])+2 

fn' n=(foldl mprod 1 (map fn' [1..n-1]))+2

