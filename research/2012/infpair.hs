module InfPair where
import Visuals
--import Pi

nAdicCons :: N->(N,N)->N
nAdicCons b (x,y')  | b>1 = (b^x)*y where
  q = y' `div` (b-1)
  y = y'+q+1

nAdicDeCons :: N->N->(N,N)
nAdicDeCons b z | b>1 && z>0 = (x,y') where
  hd n = if n `mod` b > 0 then 0 else 1+hd (n `div` b)
  x = hd z
  y = z `div` (b^x)
  q = y `div` b
  y' = y-q-1 

nAdicHead, nAdicTail :: N->N->N
nAdicHead b = fst . nAdicDeCons b
nAdicTail b = snd . nAdicDeCons b

nAdicUnPair :: N->N->(N,N)
nAdicUnPair b n = nAdicDeCons b (n+1)

nAdicPair :: N->(N,N)->N
nAdicPair b xy = (nAdicCons b xy)-1

nat2nats :: N->N->[N]
nat2nats _ 0 = []
nat2nats k n | n>0 = nAdicHead k n : nat2nats k (nAdicTail k n)

nats2nat :: N->[N]->N
nats2nat _ [] = 0
nats2nat k (x:xs) = nAdicCons k (x,nats2nat k xs)

nAdicNat :: N->Encoder N
nAdicNat k = Iso (nat2nats k) (nats2nat k)

nat :: Encoder N
nat = nAdicNat 2

nAdicBij :: N -> N -> N -> N
nAdicBij k l = (nats2nat l) . (nat2nats k) 

nAdicNats :: [N]->Encoder N
nAdicNats ks = Iso (nat2nAdicNats ks) (nAdicNats2nat ks)

nat2nAdicNats :: [N]->N->[N]
nat2nAdicNats _ 0 = []
nat2nAdicNats (k:ks) n | n>0 = 
  nAdicHead k n : nat2nAdicNats ks (nAdicTail k n)

nAdicNats2nat :: [N]->[N]->N
nAdicNats2nat _ [] = 0
nAdicNats2nat (k:ks) (x:xs) = 
  nAdicCons k (x,nAdicNats2nat ks xs)

nat' :: Encoder N
nat' = nAdicNats [2..]

list2bins :: [N]->[N]

list2bins [] = [0]
list2bins ns = f ns where
  f [] = []
  f (x:xs) = (repl x 0) ++ (1:f xs) where
    repl n a | n <= 0 = []
    repl n a = a:repl (pred n) a

bins2list :: [N] -> [N]
bins2list xs = f xs 0 where
  f [] _ = []
  f (0:xs) k = f xs (k+1)
  f (1:xs) k = k : f xs 0

bins :: Encoder [N]
bins = Iso bins2list list2bins

bsplit :: [N] -> [N] -> ([N], [N])
bsplit _ [] = ([],[])
bsplit (0:bs) (n:ns) = (xs,n:ys) where (xs,ys) = bsplit bs ns 
bsplit (1:bs) (n:ns) = (n:xs,ys) where (xs,ys) = bsplit bs ns 

bmerge :: [N] -> ([N], [N]) -> [N]
bmerge _ ([],[]) = []
bmerge bs ([],[y]) = [y]
bmerge bs ([x],[]) = [x]
bmerge bs ([],ys) = bmerge bs ([0],ys)
bmerge bs (xs,[]) = bmerge bs (xs,[0])
bmerge (0:bs) (xs,y:ys) = y : bmerge bs (xs,ys)
bmerge (1:bs) (x:xs,ys) = x : bmerge bs (xs,ys)

genericUnpair :: Encoder t -> t ->   N -> (N, N)
genericUnpair xEncoder xs n = (l,r) where 
  bs = as bins xEncoder xs
  ns = as bins nat n
  (ls,rs) = bsplit bs ns
  l = as nat bins ls
  r = as nat bins rs

genericPair :: Encoder t -> t ->   (N, N) -> N
genericPair xEncoder xs (l,r) = n where
  bs = as bins xEncoder xs
  ls = as bins nat l
  rs = as bins nat r
  ns = bmerge bs (ls,rs)
  n = as nat bins ns

bunpair2 = genericUnpair bins (cycle [1,0])
bpair2 = genericPair bins (cycle [1,0])

bpair k = genericPair set [0,k..]
bunpair k = genericUnpair set [0,k..] 

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
as that this x = g x where Iso _ g = compose that (invert this)

borrow_from :: Encoder a -> (a -> a -> a) -> 
               Encoder b -> (b -> b -> b)
borrow_from lender op borrower x y = as borrower lender
   (op (as lender borrower x) (as lender borrower y))

list :: Encoder [N]
list = itself

mset :: Encoder [N]
mset = Iso mset2list list2mset

mset2list, list2mset :: [N]->[N]
mset2list xs = zipWith (-) (xs) (0:xs)
list2mset ns = tail (scanl (+) 0 ns) 

set :: Encoder [N]
set = Iso set2list list2set

set2list, list2set :: [N]->[N]
list2set = (map pred) . list2mset . (map succ)
set2list = (map pred) . mset2list . (map succ) 

syracuse :: N->N
syracuse n = nAdicTail 2 (6*n+4)

nsyr 0 = [0]
nsyr n = n : nsyr (syracuse n)

syrnats = map syracuse [0..]

syrpair = genericPair list syrnats
syrunpair = genericUnpair list syrnats 

sqpair = genericPair set (map (^2) [0..])
squnpair = genericUnpair set (map (^2) [0..]) 

npair = genericPair list [0..]
nunpair = genericUnpair list [0..] 

bnats = concatMap (as bins nat) [0..]

bnatpair = genericPair bins bnats
bnatunpair = genericUnpair bins bnats 

{-
-- add "import Pi" to the top of this file
-- using PI as a source of a bitstream
bin_pi = as bins nat (machin_pi (2^12))

pi_pair = genericPair bins bin_pi
pi_unpair = genericUnpair bins bin_pi 
-}

