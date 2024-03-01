module OBDT where
import Data.List
import Data.Bits
import Random

type Nat = Integer
type Nat2 = (Nat,Nat)

bitpair ::  Nat2 -> Nat
bitunpair :: Nat->Nat2

bitpair (x,y) = (inflate x) .|. (inflate' y)
bitunpair z = (deflate z, deflate' z)

inflate 0 = 0
inflate n = twice (twice (inflate (half n))) .|. (parity n)

deflate 0 = 0
deflate n = twice (deflate (half (half n))) .|. (parity n)

deflate' z = half (deflate (twice z))
inflate' = twice . inflate

half n = shiftR n 1 :: Nat
twice n = shiftL n 1 :: Nat
parity n = n .&. 1 :: Nat

data BT a = B0 | B1 | D a (BT a) (BT a) deriving (Eq,Ord,Read,Show)

data OBDT a = OBDT a (BT a) deriving (Eq,Ord,Read,Show)

unfold_obdt :: Nat2 -> OBDT Nat
unfold_obdt (n,tt) = OBDT n bt where 
  bt=if tt<max then unfold_with bitunpair n tt
     else error ("unfold_obdt: last arg "++ (show tt)++
                 " should be < " ++ (show max))
     where max = 2^2^n

  unfold_with _ n 0 | n<1 =  B0
  unfold_with _ n 1 | n<1 =  B1
  unfold_with f n tt = 
    D k (unfold_with f k tt1) (unfold_with f k tt2) where
      k=pred n
      (tt1,tt2)=f tt

fold_obdt :: OBDT Nat -> Nat2
fold_obdt (OBDT n bt) = (n,(fold_with bitpair bt)) where
    fold_with rf B0 = 0
    fold_with rf B1 = 1
    fold_with rf (D _ l r) = 
      rf ((fold_with rf l),(fold_with rf r))

if_then_else 0 _ z = z
if_then_else 1 y _ = y

vn 1 0 = 1
vn n q | q==pred n = bitpair (vn n 0,0)
vn n q  | q>=0 && q < n' = 
    bitpair (q',q') where
      n'=pred n
      q'=vn n' q
 
vm n = vn (succ n) 0

eval_obdt (OBDT n bt) = eval_with_mask (vm n) n bt
 
eval_with_mask m _ B0 = 0 
eval_with_mask m _ B1 = m
eval_with_mask m n (D x l r) = 
  ite_ (vn n x) 
         (eval_with_mask m n l) 
         (eval_with_mask m n r) 

ite_ x t e = ((t `xor` e).&.x) `xor` e

bsum 0 = 0
bsum n | n>0 = bsum1 (n-1)

bsum1 0 = 2
bsum1 n | n>0 = bsum1 (n-1)+ 2^2^n

bsums = map bsum [0..]

to_bsum n = (k,n-m) where 
  k=pred (head [x|x<-[0..],bsum x>n])
  m=bsum k

nat2obdt n = unfold_obdt (k,n_m)
  where (k,n_m)=to_bsum n

obdt2nat obdt@(OBDT nv _) =  ((bsum nv)+tt) where
   (_,tt) =fold_obdt obdt

ev_obdt2nat obdt@(OBDT nv _) = (bsum nv)+(eval_obdt obdt)

obdt_reduce (OBDT n bt) = OBDT n (reduce bt) where
  reduce B0 = B0
  reduce B1 = B1
  reduce (D _ l r) | l == r = reduce l
  reduce (D v l r) = D v (reduce l) (reduce r)

unfold_robdt = obdt_reduce . unfold_obdt  

nat2robdt = obdt_reduce . nat2obdt 

obdt_size (OBDT _ t) = 1+(size t) where
  size B0 = 1
  size B1 = 1
  size (D _ l r) = 1+(size l)+(size r)

to_obdt vs tt | 0<=tt && tt <= m = 
  OBDT n (to_obdt_mn vs tt m n) where
    n=genericLength vs
    m=vm n
to_obdt _ tt = error ("bad arg in to_obdt=>" ++ (show tt)) 

to_obdt_mn []      0 _ _ = B0
to_obdt_mn []      _ _ _ = B1
to_obdt_mn (v:vs) tt m n = D v l r where
  cond=vn n v
  f0= (m `xor` cond) .&. tt
  f1= cond .&. tt 
  l=to_obdt_mn vs f1 m n
  r=to_obdt_mn vs f0 m n

to_robdt vs tt = obdt_reduce (to_obdt vs tt)
from_obdt obdt = eval_obdt obdt

search_obdt minORmax n tt = snd $ foldl1 minORmax 
 (map (sized_robdt tt) (all_permutations n)) where
    sized_robdt tt vs = (obdt_size b,b) where 
      b=to_robdt vs tt
 
all_permutations n = permute [0..n-1] where

  permute [] = [[]]
  permute (x:xs) = [zs| ys<-permute xs, zs<-insert x ys]

  insert a [] = [[a]]
  insert a (x:xs) = (a:x:xs):[(x:ys) | ys<-insert a xs]

data MT a = L a | M a (MT a) (MT a) 
             deriving (Eq,Ord,Read,Show)
data MTOBDT a = MTOBDT a a (MT a) deriving (Show,Eq)

to_mtobdt m n tt = MTOBDT m n r where 
  mlimit=2^m
  nlimit=2^n
  ttlimit=mlimit^nlimit
  r=if tt<ttlimit 
    then (to_mtobdt_ mlimit n tt)
    else error ("bt: last arg "++ (show tt)++
                " should be < " ++ (show ttlimit))

to_mtobdt_ mlimit n tt|(n<1)&&(tt<mlimit) = L tt
to_mtobdt_ mlimit n tt = (M k l r) where 
   (x,y)=bitunpair tt
   k=pred n
   l=to_mtobdt_ mlimit k x
   r=to_mtobdt_ mlimit k y

from_mtobdt (MTOBDT m n b) = from_mtobdt_ (2^m) n b

from_mtobdt_ mlimit n (L tt)|(n<1)&&(tt<mlimit)=tt
from_mtobdt_ mlimit n (M _ l r) = tt where 
   k=pred n
   x=from_mtobdt_ mlimit k l
   y=from_mtobdt_ mlimit k r
   tt=bitpair (x,y)

nrandom_nats smallest largest n seed= 
  genericTake n 
    (randomRs (smallest,largest) (mkStdGen seed))

nrandom converter smallest largest n seed =
  map converter (nrandom_nats smallest largest n seed)

