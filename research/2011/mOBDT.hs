module BP where
import Data.Bits

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
  n = length vs
 
eval_with_mask m _ O = 0 
eval_with_mask m _ I = m
eval_with_mask m (v:vs) (D l r) = 
  ite_ v (eval_with_mask m vs l) (eval_with_mask m vs r) 

ite_ x t e = ((t `xor` e).&.x) `xor` e

eval_obdt bt = eval_obdt_with (reverse [0..(bdepth bt)-1]) bt

