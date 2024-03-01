module MPrimes where
import Data.List

-- import Visuals

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

xunpair :: N->N->(N,N)
xunpair b n = xdecons b (n+1)

xpair :: N->(N,N)->N
xpair b xy = (xcons b xy)-1


nat2nats :: N->N->[N]
nat2nats _ 0 = []
nat2nats k n | n>0 = xhd k n : nat2nats k (xtl k n)

nats2nat :: N->[N]->N
nats2nat _ [] = 0
nats2nat k (x:xs) = xcons k (x,nats2nat k xs)

xnat :: N->Encoder N
xnat k = Iso (nat2nats k) (nats2nat k)

nat :: Encoder N
nat = xnat 2

nat2ynats :: [N]->N->[N]
nat2ynats _ 0 = []
nat2ynats (k:ks) n | n>0 = xhd k n : nat2ynats ks (xtl k n)

ynats2nat :: [N]->[N]->N
ynats2nat _ [] = 0
ynats2nat (k:ks) (x:xs) = xcons k (x,ynats2nat ks xs)

ynat :: [N]->Encoder N
ynat ks = Iso (nat2ynats ks) (ynats2nat ks)

nat' :: Encoder N
nat' = ynat [2..]

pnat :: Encoder N
pnat = ynat primes

xbij :: N -> N -> N -> N
xbij k l = (nats2nat l) . (nat2nats k) 

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

nat2mset1 n = map succ (as mset0 nat (pred n))
mset2nat1 ns = succ (as nat mset0 (map pred ns)) 

mset :: Encoder [N]
mset = compose (Iso mset2nat1 nat2mset1) nat

mprod = borrow_from mset msetSum nat

mprod_alt n m = as nat mset (msetSum (as mset nat n) (as mset nat m))

mproduct ns = foldl mprod 1 ns

pmprod n m = as nat pmset (msetSum (as pmset nat n) (as pmset nat m))

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

class Converter m where
  lift :: N->m N
  unlift :: m N -> N
  
  mix :: [m N]->m N 
  unmix :: m N->[m N]

  unlifts :: [m N] -> [N]
  unlifts xs = map unlift xs
  
  lifts :: [N] -> [m N]
  lifts xs = map lift xs

  mixWith :: ([N]->N)->([m N]->m N)
  mixWith f = lift . f . unlifts
  
  unmixWith :: (N->[N])->(m N->[m N])    
  unmixWith f = map lift . f . unlift

  as_xmset :: m N -> [m N]
  as_xmset = lifts . list2mset . unlifts . unmix 

  is_xprime :: m N -> Bool
  is_xprime x = 1==length (as_xmset x)
    
  xprimes_from :: m N->[m N]
  xprimes_from x =  filter is_xprime (iterate (lift . succ . unlift) x) 

  from_xpos :: m N -> m N
  from_xpos x = from_pos_in (xprimes_from (lift 1)) (unlift x)

  to_xprimes :: m N->[m N]
  to_xprimes x = map from_xpos (as_xmset x)

data P a = P a deriving (Show, Read, Eq, Ord)

mixP = pmset2nat . list2mset
unmixP = mset2list . nat2pmset

instance Converter P where
   mix  = mixWith mixP
   unmix = unmixWith unmixP
    
   lift n = P n
   unlift (P n) = n

   from_xpos (P n) = P (from_pos_in primes (pred n))

data X2 a = X2 a deriving (Show, Read, Eq, Ord)
instance Converter X2 where
  lift n = X2 (succ n)
  unlift (X2 n) = pred n

  mix = mixWith (mixX 2)
  unmix = unmixWith (unmixX 2)

bigomega t m = map  (length . as_xmset . t) [1..2^m]    
omega t m = map  (length . nub . as_xmset . t) [1..2^m] 

bigomega_sum t m = scanl (+) 0 (bigomega t m)    
omega_sum t m = scanl (+) 0 (omega t m)

isBsmooth :: (Converter m, Ord (m N)) => m N -> m N -> Bool
isBsmooth b n = []==filter (>b) (to_xprimes n)

smooth_set :: (Converter m, Ord (m N)) => m N -> N -> [N]
smooth_set b m = unlifts (filter (isBsmooth b) (lifts [2..2^m])) 

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

borrow_from :: Encoder a -> (a -> a -> a) -> Encoder b -> (b -> b -> b)
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

msetSum xs ys = sort (xs ++ ys)

msetSymDif xs ys = msetSum (msetDif xs ys) (msetDif ys xs)

msetUnion xs ys = msetSum (msetSymDif xs ys) (msetInter xs ys) 

data X3 a = X3 a deriving (Show, Read, Eq, Ord)
instance Converter X3 where
  lift n = X3 (succ n)
  unlift (X3 n) = pred n

  mix = mixWith (mixX 3)
  unmix = unmixWith (unmixX 3)

data X5 a = X5 a deriving (Show, Read, Eq, Ord)
instance Converter X5 where
  lift n = X5 (succ n)
  unlift (X5 n) = pred n

  mix = mixWith (mixX 5)
  unmix = unmixWith (unmixX 5)

data X103 a = X103 a deriving (Show, Read, Eq, Ord)
instance Converter X103 where
  lift n = X103 (succ n)
  unlift (X103 n) = pred n

  mix = mixWith (mixX 103)
  unmix = unmixWith (unmixX 103)

mixX _ [] = 0
mixX k (x:xs) = xcons k (x,(mixX k xs))

unmixX _ 0 = []
unmixX k n = xhd k n : unmixX k (xtl k n)


{-
-- visuals
  
es f n = nat2es (map unlift.unmix.f) n
ess f ns = sort (nub (concatMap (es f) ns))
mess f m = ess f [0..2^m-1]
viss f = eviz . ess f
mviss f m = viss f [0..2^m-1]
 
-- ex: mviss X2 5 - lattice

-}


