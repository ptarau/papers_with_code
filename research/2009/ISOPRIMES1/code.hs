module ISOPRIMES where
import Data.List
import Data.Graph
import Data.Graph.Inductive
import Graphics.Gnuplot.Simple
import ISO0

mset :: Encoder [Nat]
mset = Iso mset2fun fun2mset

mset2fun = to_diffs . sort
to_diffs xs = zipWith (-) (xs) (0:xs)

fun2mset ns = tail (scanl (+) 0 ns) 

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

nat2mset = as mset nat
mset2nat = as nat mset 

nat2pmset 0 = []
nat2pmset n = map (to_pos_in (h:ts)) (to_factors (n+1) h ts) where
  (h:ts)=genericTake (n+1) primes
  
to_pos_in xs x = fromIntegral i where Just i=elemIndex x xs

pmset2nat [] = 0
pmset2nat ns = (product ks)-1 where
  ks=map (from_pos_in ps) ns
  ps=primes
  from_pos_in xs n = xs !! (fromIntegral n)

pmset :: Encoder [Nat]
pmset = compose (Iso pmset2nat nat2pmset) nat

mprod = borrow_from mset (++) nat

mprod_alt n m = as nat mset ((as mset nat n) ++ (as mset nat m))

mexp n 0 = 0
mexp n k = mprod n (mexp n (k-1))

pmprod n m = as nat pmset ((as pmset nat n) ++ (as pmset nat m))

pmprod' n m = (n+1)*(m+1)-1

mprod' 0 _ = 0
mprod' _ 0 = 0
mprod' m n = (mprod (n-1) (m-1)) + 1

mexp' n 0 = 1
mexp' n k = mprod' n (mexp' n (k-1))

mgcd :: Nat -> Nat -> Nat
mgcd = borrow_from mset msetInter nat

mlcm :: Nat -> Nat -> Nat
mlcm = borrow_from mset msetUnion nat

mdiv :: Nat -> Nat -> Nat
mdiv = borrow_from mset msetDif nat

is_mprime p = []==[n|n<-[1..p-1],n `mdiv` p==0]

mprimes = filter is_mprime [1..]

primes = 2 : filter is_prime [3,5..]

is_prime p = [p]==to_primes p

to_primes n | n>1 = to_factors n p ps where 
  (p:ps) = primes

to_factors n p ps | p*p > n = [n]
to_factors n p ps | 0==n `mod` p = p : to_factors (n `div` p)  p ps 
to_factors n p ps@(hd:tl) = to_factors n hd tl

msetInter [] _ = []
msetInter _ [] = []
msetInter (x:xs) (y:ys) | x==y = (x:zs) where zs=msetInter xs ys
msetInter (x:xs) (y:ys) | x<y = msetInter xs (y:ys)
msetInter (x:xs) (y:ys) | x>y = msetInter (x:xs) ys

msetDif [] _ = []
msetDif xs [] = xs
msetDif (x:xs) (y:ys) | x==y = zs where zs=msetDif xs ys
msetDif (x:xs) (y:ys) | x<y = (x:zs) where zs=msetDif xs (y:ys)
msetDif (x:xs) (y:ys) | x>y = zs where zs=msetDif (x:xs) ys

msetSymDif xs ys = sort ((msetDif xs ys) ++ (msetDif ys xs))

msetUnion xs ys = sort ((msetDif xs ys) ++ (msetInter xs ys) ++ (msetDif ys xs))

