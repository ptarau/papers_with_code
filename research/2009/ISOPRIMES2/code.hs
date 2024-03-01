module ISOPRIMES where
import Data.List
import Data.Bits
import Ratio
import Random
import ISO0

type Nat2 = (Nat,Nat)

bitpair ::  Nat2 -> Nat
bitpair (i,j) = 
  set2nat ((evens i) ++ (odds j)) where
    evens x = map (2*) (nat2set x)
    odds y = map succ (evens y)

bitunpair :: Nat->Nat2  
bitunpair n = (f xs,f ys) where 
  (xs,ys) = partition even (nat2set n)
  f = set2nat . (map (`div` 2))

nat2 :: Encoder Nat2
nat2 = compose (Iso bitpair bitunpair) nat

pair2unord_pair (x,y) = fun2set [x,y]
unord_pair2pair [a,b] = (x,y) where 
  [x,y]=set2fun [a,b]   

unord_unpair = pair2unord_pair . bitunpair
unord_pair = bitpair . unord_pair2pair

set2 :: Encoder [Nat]
set2 = compose (Iso unord_pair2pair pair2unord_pair) nat2

pair2mset_pair (x,y) = (a,b) where [a,b]=fun2mset [x,y]
mset_unpair2pair (a,b) = (x,y) where [x,y]=mset2fun [a,b]

mset_unpair = pair2mset_pair . bitunpair
mset_pair = bitpair . mset_unpair2pair

mset2 :: Encoder Nat2
mset2 = compose (Iso mset_unpair2pair pair2mset_pair) nat2

bitlift x = bitpair (x,0)
bitlift' = (from_base 4) . (to_base 2)

bitclip = fst . bitunpair
bitclip' = (from_base 2) . (map (`div` 2)) . (to_base 4) . (*2)

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

mset_pair' (a,b) = bitpair (min a b, (max a b) - (min a b)) 

mset_pair'' (a,b) = unord_pair [min a b, (max a b)+1]

unord_pair' [a,b] = bitpair (min a b, (max a b) - (min a b) -1) 

unord_pair'' [a,b] = mset_pair (min a b, (max a b)-1)

ppair pairingf (p1,p2) | is_prime p1 && is_prime p2 = 
  from_pos_in ps (pairingf (to_pos_in ps p1,to_pos_in ps p2)) where 
    ps = primes

to_pos_in xs x = fromIntegral i where Just i=elemIndex x xs
from_pos_in xs n = xs !! (fromIntegral n)
  
punpair unpairingf p | is_prime p = (from_pos_in ps n1,from_pos_in ps n2) where 
  ps=primes
  (n1,n2)=unpairingf (to_pos_in ps p)

hyper_primes u = [n|n<-primes, all_are_primes (uparts u n)] where
  all_are_primes ns = and (map is_prime ns)
  
uparts u = sort . nub . tail . (split_with u) where
    split_with _ 0 = []
    split_with _ 1 = []
    split_with u n = n:(split_with u n0)++(split_with u n1) where
      (n0,n1)=u n  

set2fun xs = shift_tail pred (mset2fun xs) where
  shift_tail _ [] = []
  shift_tail f (x:xs) = x:(map f xs)

fun2set = (map pred) . fun2mset . (map succ)

set :: Encoder [Nat]
set = Iso set2fun fun2set

nat_set = Iso nat2set set2nat 

nat2set n | n>=0 = nat2exps n 0 where
  nat2exps 0 _ = []
  nat2exps n x = if (even n) then xs else (x:xs) where
    xs=nat2exps (n `div` 2) (succ x)

set2nat ns = sum (map (2^) ns)

nat :: Encoder Nat
nat = compose nat_set set

mset2fun = to_diffs . sort
to_diffs xs = zipWith (-) (xs) (0:xs)

fun2mset ns = tail (scanl (+) 0 ns) 

mset :: Encoder [Nat]
mset = Iso mset2fun fun2mset

primes = 2 : filter is_prime [3,5..]

is_prime p = [p]==to_primes p

to_primes n | n>1 = to_factors n p ps where 
  (p:ps) = primes

to_factors n p ps | p*p > n = [n]
to_factors n p ps | 0==n `mod` p = p : to_factors (n `div` p)  p ps 
to_factors n p ps@(hd:tl) = to_factors n hd tl

to_base base n = d : 
  (if q==0 then [] else (to_base base q)) where
     (q,d) = quotRem n base

from_base base [] = 0
from_base base (x:xs) | x>=0 && x<base = 
   x+base*(from_base base xs)

