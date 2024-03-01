module BP where
import Data.List
import Data.Bits
import Random

type N = Integer

bitpair ::  (N,N) -> N
bitunpair :: N->(N,N)

bitpair (x,y) = inflate x .|. inflate' y
bitunpair z = (deflate z, deflate' z)

inflate,deflate :: N -> N

inflate 0 = 0
inflate n = (twice . twice . inflate . half) n .|. firstBit n

deflate 0 = 0
deflate n = (twice . deflate . half . half) n .|. firstBit n

deflate' = half . deflate . twice
inflate' = twice . inflate

half n = shiftR n 1 :: N
twice n = shiftL n 1 :: N
firstBit n = n .&. 1 :: N

data BT = O | I | D BT BT deriving (Eq,Ord,Read,Show)

bdepth O = 0
bdepth I = 0
bdepth (D x _) = 1 + (bdepth x)

unfold_bt :: (N,N) -> BT
unfold_bt (n,tt) = if tt<2^2^n 
  then unfold_with bitunpair n tt
  else undefined where
    unfold_with _ n 0 | n<1 =  O
    unfold_with _ n 1 | n<1 =  I
    unfold_with f n tt = 
      D (unfold_with f k tt1) (unfold_with f k tt2) where
        k=pred n
        (tt1,tt2)=f tt

fold_bt :: BT -> (N,N)
fold_bt bt = (n,fold_with bitpair bt) where
    n = bdepth bt
    fold_with f O = 0
    fold_with f I = 1
    fold_with f (D l r) = f (fold_with f l,fold_with f r)

if_then_else 0 _ z = z
if_then_else 1 y _ = y

vn :: N->N->N
vn 1 0 = 1
vn n q | q == pred n = bitpair (vn n 0,0)
vn n q  | q>=0 && q < n' = bitpair (q',q') where
  n' = pred n
  q' = vn n' q

vm :: N->N 
vm n = vn (n+1) 0

eval_obdt_with :: [N]->BT->N
eval_obdt_with vs bt = eval_with_mask (vm n) (map (vn n) vs) bt where
  n = genericLength vs
 
eval_with_mask m _ O = 0 
eval_with_mask m _ I = m
eval_with_mask m (v:vs) (D l r) = 
  ite_ v (eval_with_mask m vs l) (eval_with_mask m vs r) 

ite_ :: N->N->N->N
ite_ x t e = ((t `xor` e).&.x) `xor` e

eval_obdt :: BT -> N
eval_obdt bt = eval_obdt_with (reverse [0..(bdepth bt)-1]) bt

bsum :: N->N
bsum 0 = 0
bsum n | n>0 = bsum1 (n-1)

bsum1 0 = 2
bsum1 n | n>0 = bsum1 (n-1)+ 2^2^n

bsums = map bsum [0..]

to_bsum n = (k,n-m) where 
  k=pred (head [x|x<-[0..],bsum x>n])
  m=bsum k

nat2obdt n = unfold_bt (k,n_m) where (k,n_m) = to_bsum n

obdt2nat obdt =  (bsum nv) + tt where
  nv = bdepth obdt
  (_,tt) = fold_bt obdt
 

ev_obdt2nat obdt = (bsum nv)+(eval_obdt obdt) where
  nv = bdepth obdt

to_obdt vs tt | 0<=tt && tt <= m = 
  to_obdt_mn vs tt m n where
    n=genericLength vs
    m=vm n
to_obdt _ tt = error ("bad arg in to_obdt=>" ++ (show tt)) 

to_obdt_mn []      0 _ _ = O
to_obdt_mn []      _ _ _ = I
to_obdt_mn (v:vs) tt m n = D l r where
  cond=vn n v
  f0= (m `xor` cond) .&. tt
  f1= cond .&. tt 
  l=to_obdt_mn vs f1 m n
  r=to_obdt_mn vs f0 m n

data MT a = L a | M a (MT a) (MT a) 
             deriving (Eq,Ord,Read,Show)
data MTOBDT a = MTOBDT a a (MT a) deriving (Show,Eq)

to_mtobdt :: N -> N -> N -> MTOBDT N
to_mtobdt m n tt = MTOBDT m n r where 
  mlimit=2^m
  nlimit=2^n
  ttlimit=mlimit^nlimit
  r=if tt<ttlimit 
    then (to_mtobdt_ mlimit n tt)
    else error ("bt: last arg "++ (show tt)++
                " should be < " ++ (show ttlimit))

to_mtobdt_ :: N -> N -> N -> MT N
to_mtobdt_ mlimit n tt|(n<1)&&(tt<mlimit) = L tt
to_mtobdt_ mlimit n tt = (M k l r) where 
   (x,y)=bitunpair tt
   k=pred n
   l=to_mtobdt_ mlimit k x
   r=to_mtobdt_ mlimit k y

from_mtobdt :: MTOBDT N -> N
from_mtobdt (MTOBDT m n b) = from_mtobdt_ (2^m) n b

from_mtobdt_ :: N -> N -> MT N -> N
from_mtobdt_ mlimit n (L tt)|(n<1)&&(tt<mlimit)=tt
from_mtobdt_ mlimit n (M _ l r) = tt where 
   k=pred n
   x=from_mtobdt_ mlimit k l
   y=from_mtobdt_ mlimit k r
   tt=bitpair (x,y)

nrandom_nats :: (Random a) => a -> a -> N -> Int -> [a]
nrandom_nats smallest largest n seed = genericTake n 
    (randomRs (smallest,largest) (mkStdGen seed))

nrandom :: (Random a) => (a -> b) -> a -> a -> N -> Int -> [b]
nrandom converter smallest largest n seed =
  map converter (nrandom_nats smallest largest n seed)

