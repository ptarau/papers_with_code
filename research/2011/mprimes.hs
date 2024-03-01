module MPrimes where
import Data.List

--import Visuals

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

nat2pmset 1 = []
nat2pmset n = to_prime_positions n

pmset2nat [] = 1
pmset2nat ns = product (map (from_pos_in primes . pred) ns)

pmset :: Encoder [N]
pmset = compose (Iso pmset2nat nat2pmset) nat

mset2list xs = zipWith (-) (xs) (0:xs)

list2mset ns = tail (scanl (+) 0 ns) 

mset0 :: Encoder [N]
mset0 = Iso mset2list list2mset

nat2mset1 n=map succ (as mset0 nat (pred n))
mset2nat1 ns=succ (as nat mset0 (map pred ns)) 

mset :: Encoder [N]
mset = compose (Iso mset2nat1 nat2mset1) nat

mprod = borrow_from mset sortedConcat nat

mprod_alt n m = as nat mset 
  (sortedConcat (as mset nat n) (as mset nat m))

mproduct ns = foldl mprod 1 ns

pmprod n m = as nat pmset 
  (sortedConcat (as pmset nat n) (as pmset nat m))

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

mobius t n = if nub ns == ns then f ns else 0 where 
  ns = as t nat n
  f ns = if even (genericLength ns) then 1 else -1    

mertens t n = sum (map (mobius t) [1..n])

mertens2 t n = m^2 where m = mertens t n
 
counterex_mertens t m = [n|n<-[2..m],mertens2 t n >= n^2]

mlt k m = [n|n<-[k..m],mertens2 mset n< mertens2 pmset n]
meq k m = [n|n<-[k..m],mertens2 mset n==mertens2 pmset n]
mgt k m = [n|n<-[k..m],mertens2 mset n>mertens2 pmset n]

auto_m2p 0 = 0   
auto_m2p n = as nat pmset (as mset nat n) 

auto_p2m 0 = 0
auto_p2m n = as nat mset (as pmset nat n)

mprod' 0 _ = 0
mprod' _ 0 = 0
mprod' x y | x>0 && y>0= mprod x y

emulated_mprod' x y = 
  auto_p2m ((auto_m2p x) * (auto_m2p y))

emulated_prod x y = 
  auto_m2p (mprod (auto_p2m x) (auto_p2m y))

lt_mp n = length [x|x<-[0..n],auto_m2p x < auto_p2m x]
eq_mp n = length [x|x<-[0..n],auto_m2p x == auto_p2m x]
gt_mp n = length [x|x<-[0..n],auto_m2p x > auto_p2m x]

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

primes = 2 : filter is_prime [3,5..]

is_prime p = [p]==to_primes p

to_primes n|n>1 = to_factors n p ps where (p:ps) = primes

to_factors n p ps | p*p > n = [n]
to_factors n p ps | 0==n `mod` p = 
  p : to_factors (n `div` p)  p ps 
to_factors n p ps@(hd:tl) = to_factors n hd tl

to_prime_positions n = 
  map (succ . (to_pos_in (h:ps))) qs where
    (h:ps)=genericTake n primes
    qs=to_factors n h ps
   
to_pos_in xs x = fromIntegral i where 
  Just i=elemIndex x xs

from_pos_in xs n = xs !! (fromIntegral n)   

msetInter, msetDif, msetSymDif, msetUnion :: 
  (Ord a) => [a] -> [a] -> [a]

msetInter [] _ = []
msetInter _ [] = []
msetInter (x:xs) (y:ys) | x==y = x:msetInter xs ys
msetInter (x:xs) (y:ys) | x<y = msetInter xs (y:ys)
msetInter (x:xs) (y:ys) | x>y = msetInter (x:xs) ys

msetDif [] _ = []
msetDif xs [] = xs
msetDif (x:xs) (y:ys) | x==y = msetDif xs ys
msetDif (x:xs) (y:ys) | x<y = x:msetDif xs (y:ys)
msetDif (x:xs) (y:ys) | x>y = msetDif (x:xs) ys

msetSymDif xs ys = 
  sortedConcat (msetDif xs ys) (msetDif ys xs)

msetUnion xs ys = 
  sortedConcat (msetSymDif xs ys) (msetInter xs ys) 

sortedConcat xs ys = sort (xs ++ ys)

