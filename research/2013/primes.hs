module Primes where
import Data.List

--import Visuals

type N = Integer

toBijBase :: N->N->[N]
toBijBase _ 0 = []
toBijBase b n | n>0 = d : ds where
  (d,m) = getBijDigit b n
  ds = toBijBase b m

fromBijBase :: N->[N]->N  
fromBijBase _ [] = 0
fromBijBase b (d:ds) = n where
  m = fromBijBase b ds
  n = putBijDigit b d m  

getBijDigit :: N->N->(N,N)  
getBijDigit b n | n>0 = 
  if d == 0 then (b-1,q-1) else (d-1,q) where
    (q,d) = quotRem n b

putBijDigit :: N->N->N->N
putBijDigit b d m | 0 <= d && d < b = 1+d+b*m  

nat2nats _ 0 = []
nat2nats _ 1 = [0]
nat2nats k n | n>0 = ns where 
  n' = pred n
  k' = succ k
  xs = toBijBase k' n' 
  nss = splitWith k xs
  ns = map (fromBijBase k) nss

  splitWith sep xs =  y : f ys where
   (y, ys) = break (==sep) xs

   f [] = []
   f (_:zs) = splitWith sep zs

nats2nat _ [] = 0
nats2nat _ [0] = 1
nats2nat k ns = n where
  nss = map (toBijBase k) ns
  xs = intercalate [k] nss 
  n' = fromBijBase (succ k) xs
  n = succ n'

xcons :: N->(N,N)->N
xcons b (x,y')  | b>1 = (b^x)*y where
  q=y' `div` (b-1)
  y=y'+q+1
  
xdecons :: N->N->(N,N)
xdecons b z | b>1 && z>0 = (x,y') where
  hd n = if n `mod` b > 0 then 0 else 1+hd (n `div` b)
  x = hd z
  y = z `div` (b^x)
  q = y `div` b
  y' = y-q-1 

xhd, xtl :: N->N->N
xhd b = fst . xdecons b
xtl b = snd . xdecons b

nat2xnats :: N->N->[N]
nat2xnats _ 0 = []
nat2xnats k n | n>0 = xhd k n : nat2xnats k (xtl k n)

xnats2nat :: N->[N]->N
xnats2nat _ [] = 0
xnats2nat k (x:xs) = xcons k (x,xnats2nat k xs)

nat2znats :: N->N->[N]
nat2znats _ 0 = []
nat2znats k n | n>0 = xhd k n : nat2znats (succ k) (xtl k n)

znats2nat :: N->[N]->N
znats2nat _ [] = 0
znats2nat k (x:xs) = xcons k (x,znats2nat (succ k) xs)

mset2list xs = zipWith (-) (xs) (0:xs)

list2mset ns = tail (scanl (+) 0 ns) 

nat2pmset 1 = []
nat2pmset n | n>1  = map succ (to_prime_positions n)

pmset2nat [] = 1
pmset2nat ns = from_prime_positions (map pred ns)

nat2plist = mset2list . map pred. nat2pmset . succ
plist2nat = pred . pmset2nat . map succ . list2mset 

class Converter m where
  lift :: N->m N
  unlift :: m N -> N
  
  mix :: [m N]->m N 
  unmix :: m N->[m N]

  unlifts :: [m N] -> [N]
  unlifts = map unlift
  
  lifts :: [N] -> [m N]
  lifts = map lift 

  mixWith :: ([N]->N)->([m N]->m N)
  mixWith f = lift . f . unlifts
  
  unmixWith :: (N->[N])->(m N->[m N])    
  unmixWith f = lifts . f . unlift

  liftFun:: (N->N) -> m N-> m N
  liftFun f = lift.f.unlift
      
  liftFuns:: ([N]->[N]) -> [m N]-> [m N]
  liftFuns f = lifts.f.unlifts

  to_xmset :: m N -> [m N]
  to_xmset = liftFuns (map succ . list2mset) . unmix
  
  from_xmset :: [m N] -> m N
  from_xmset = mix . liftFuns (mset2list . map pred)

-- alternative, from 0
  to_xmset0 :: m N -> [m N]
  to_xmset0 = (liftFuns list2mset) . unmix
  
  from_xmset0 :: [m N] -> m N
  from_xmset0 = mix . (liftFuns mset2list)

  is_xprime :: m N -> Bool
  is_xprime x = f xs where
    xs = to_xmset (liftFun pred x)
    f [p] = True
    f _ = False
    
  xprimes_from :: m N->[m N]
  xprimes_from x =  filter is_xprime 
    (iterate (liftFun succ) x) 

  from_xindices :: [m N]->m N
  from_xindices = (liftFun succ) . from_xmset

  to_xindices :: m N->[m N]
  to_xindices  = to_xmset . (liftFun pred)
  
  to_xfactors :: m N->[m N]
  to_xfactors x = map i2f (to_xindices x) where
    ps = xprimes_from (lift 1)
    i2f i = ps `genericIndex` (pred (unlift i))

data P a = P a deriving (Show, Read, Eq, Ord)

instance Converter P where
   mix  = mixWith plist2nat
   unmix = unmixWith nat2plist
    
   lift n = P n
   unlift (P n) = n

data A a = A a deriving (Show, Read, Eq, Ord)

instance Converter A where
   mix  = mixWith (nats2nat 2)
     
   unmix  = unmixWith (nat2nats 2)
        
   lift n = A n
   unlift (A n) = n  

data B a = B a deriving (Show, Read, Eq, Ord)

instance Converter B where
   mix  = mixWith (nats2nat 3)
     
   unmix  = unmixWith (nat2nats 3)
        
   lift n = B n
   unlift (B n) = n  

data X a = X a deriving (Show, Read, Eq, Ord)
instance Converter X where
  lift n = X n
  unlift (X n) = n

  mix = mixWith (xnats2nat 2)
  unmix = unmixWith (nat2xnats 2)

data Y a = Y a deriving (Show, Read, Eq, Ord)
instance Converter Y where
  lift n = Y n
  unlift (Y n) = n

  mix = mixWith (xnats2nat 3)
  unmix = unmixWith (nat2xnats 3)

data CTree = C [CTree] deriving (Show,Read,Eq)

class Converter m => CatalanView m where
  toTree :: m N -> CTree
  toTree mn = C (map toTree (unmix mn))
 
  fromTree :: CTree -> m N
  fromTree (C xs) = mix (map fromTree xs) 

  morphTree :: (CatalanView m') => m' N -> m N  
  morphTree  = fromTree . toTree 

  tsize :: (N->m N)->N-> N
  tsize t n = ts (toTree (t n)) where
   ts (C []) = 1
   ts (C xs) = succ (sum (map ts xs))

instance CatalanView P
instance CatalanView A
instance CatalanView B
instance CatalanView X
instance CatalanView Y

p n = morphTree n :: P N
a n = morphTree n :: A N
b n = morphTree n :: B N
x n = morphTree n :: X N
y n = morphTree n :: Y N

class (Ord (m N),Converter m)=>ArithOps m where
  multiply :: (m N)->(m N)->(m N) 
  multiply x y = from_xindices 
    (sort (to_xindices x ++ to_xindices y)) 

instance ArithOps P
instance ArithOps A
instance ArithOps B
instance ArithOps X
instance ArithOps Y

repsize b n = genericLength (toBijBase b n)

bitsize = repsize 2 

class (Converter m,Ord (m N))=>Comparator m where
  infoLoss :: (N->m N)->N->N->N
  infoLoss t k n = f (unlifts.unmix.t) n where
    f u n = (repsize k n) - s where
      ns = u n
      s = sum (map (repsize k) ns)

-- an alternative, with multisets, from 0

  infoLossM :: (N->m N)->N->N->N
  infoLossM t k n = f (unlifts.to_xmset0.t) n where
    f u n = (repsize k n) - s where
      ns = u n
      s = sum (map (repsize k) ns)  
 
 -- other things to try out 
 
  repsum0 :: (N->m N)->N->N
  repsum0 t n = sum  ((unlifts.to_xmset0.t) n)


  repsum :: (N->m N)->N->N
  repsum t n = sum  ((unlifts.unmix.t) n)
    
  rad :: m N->m N  
  rad n = from_xindices (nub (to_xindices n))
  
  rad2 :: m N->m N
  rad2 n = from_xindices (intersect ns ns') where
    ns = nub (to_xindices n)
    ns' = nub (to_xindices (liftFun succ n))
    

  totalInfoLoss:: (N->m N)->N->N
  totalInfoLoss t n = sum (map (infoLoss t 2) [0..2^n-1])

  prefixSumLoss:: (N->m N)->N->[N]
  prefixSumLoss t n = 
    scanl1 (+) (map (infoLoss t 2) [0..2^n-1])

instance Comparator P
instance Comparator A
instance Comparator B
instance Comparator X
instance Comparator Y

scomp ns = (r-l,r,l) where
  l = sum (map bitsize ns)
  r = bitsize (product (map succ (list2mset ns)))
  


icomp2 t1 t2 n = [prefixSumLoss t1 n,prefixSumLoss t2 n]

icomp3 t1 t2 t3 m = 
  [prefixSumLoss t1 m,prefixSumLoss t2 m,prefixSumLoss t3 m]

t0 = map (infoLoss P) [0..2^8-1]
t1 = map (infoLoss A) [0..2^8-1]
t2 = map (infoLoss X) [0..2^8-1]

t3 = icomp3 Y X P 14 -- !
t4 = icomp3 A P B 16 -- !
t5 = icomp2 A P 19
t6 = icomp2 B P 20
t7 = icomp2 B P 21 -- !

bigomega :: Converter m => (N -> m N) -> N -> [Int]
bigomega t m = map  (length . to_xmset . t) [1..2^m]    
omega t m = map  (length . nub . to_xmset . t) [1..2^m] 


bigomega_sum :: Converter m => (N -> m N) -> N -> [Int]
bigomega_sum t m = scanl (+) 0 (bigomega t m)    
omega_sum t m = scanl (+) 0 (omega t m)

isBsmooth :: Comparator m => m N -> m N -> Bool
isBsmooth b n = []==filter (>b) (to_xfactors n)

smooth_set :: Comparator m => m N -> N -> [N]
smooth_set b m = 
  unlifts (filter (isBsmooth b) (lifts [2..2^m])) 

primes = 2 : filter is_prime [3,5..]

is_prime p = [p]==to_primes p

to_primes n|n>1 = 
  to_factors n p ps where (p:ps) = primes

to_factors n p ps | p*p > n = [n]
to_factors n p ps | 0==n `mod` p = 
  p : to_factors (n `div` p)  p ps 
to_factors n p ps@(hd:tl) = to_factors n hd tl

to_prime_positions n | n>1 = 
  map (to_pos_in (h:ps)) qs where
    (h:ps)=genericTake n primes
    qs=to_factors n h ps

from_prime_positions ns = product 
  (map  (from_pos_in primes) ns)
   
to_pos_in xs x = fromIntegral i where 
  Just i=elemIndex x xs

from_pos_in xs n = genericIndex xs n

