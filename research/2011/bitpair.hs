module BP where
import Data.Bits
import Data.List
--import Visuals
--import RankPerms

type N = Integer

bitpair ::  (N,N) -> N
bitunpair :: N->(N,N)

bitpair (x,y) = inflate x .|. inflate' y
bitunpair z = (deflate z, deflate' z)

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

vn 1 0 = 1
vn n q | q == pred n = bitpair (vn n 0,0)
vn n q  | q>=0 && q < n' = bitpair (q',q') where
  n' = pred n
  q' = vn n' q
 
vm n = vn (n+1) 0

eval_obdt_with vs bt = eval_with_mask (vm n) (map (vn n) vs) bt where
  n = genericLength vs
 
eval_with_mask m _ O = 0 
eval_with_mask m _ I = m
eval_with_mask m (v:vs) (D l r) = 
  ite_ v (eval_with_mask m vs l) (eval_with_mask m vs r) 

ite_ x t e = ((t `xor` e).&.x) `xor` e

eval_obdt bt = eval_obdt_with (reverse [0..(bdepth bt)-1]) bt

to_obdt vs tt | 0<=tt && tt <= m = (vs,to_obdt_mn vs tt m n) where
    n=genericLength vs
    m=vm n
to_obdt _ tt = undefined

to_obdt_mn []         0 _ _ = O
to_obdt_mn [] _PowerOf2 _ _ = I
to_obdt_mn (v:vs) tt m n = D l r where
  cond=vn n v
  f0= (m `xor` cond) .&. tt
  f1= cond .&. tt 
  l=to_obdt_mn vs f1 m n
  r=to_obdt_mn vs f0 m n

from_obdt (vs,bt) = eval_obdt_with vs bt

bsum 0 = 0
bsum n | n>0 = bsum1 (n-1)

bsum1 0 = 2
bsum1 n | n>0 = bsum1 (n-1)+ 2^2^n

bsums = map bsum [0..]

to_bsum n = (k,n-m) where 
  k=pred (head [x|x<-[0..],bsum x>n])
  m=bsum k

nat2obdt n = unfold_bt (k,n_m) where (k,n_m) = to_bsum n

obdt2nat nv =  (bsum (bdepth nv))+tt where(_,tt) = fold_bt nv

ev_obdt2nat nv = (bsum (bdepth nv))+(eval_obdt nv)


to_base base n = d : 
  (if q==0 then [] else (to_base base q)) where
     (q,d) = quotRem n base
    
from_base base [] = 0
from_base base (x:xs) | x>=0 && x<base = 
   x+base*(from_base base xs)

to_bt 0 = O
to_bt 1 = I
to_bt z = D a b where 
  (x,y)=bitunpair z
  a=to_bt x
  b=to_bt y

depth_of 0 = 0
depth_of 1 = 0
depth_of z = 1+(max a b) where 
  (x,y)=bitunpair z
  a=depth_of x
  b=depth_of y

rr O = O
rr I = I
rr (D x y) = D (rr y) x

rl O = O
rl I = I
rl (D x y) = D y (rl x)

