module Goedel where
import Data.List
import Data.Char

cons :: N->N->N
cons x y  = (2^x)*(2*y+1)

hd :: N->N
hd n | n>0 = if odd n then 0 else 1+hd  (n `div` 2)

tl :: N->N
tl n = n `div` 2^((hd n)+1)

as_nats_nat :: N->[N]
as_nats_nat 0 = []
as_nats_nat n = hd n : as_nats_nat (tl n)
 
as_nat_nats :: [N]->N  
as_nat_nats [] = 0
as_nat_nats (x:xs) = cons x (as_nat_nats xs)

nat1 :: Encoder N
nat1 = Iso as_nats_nat as_nat_nats

unpair z = (hd (z+1), tl (z+1))
pair (x,y) = (cons x y)-1

to_tuple k n = map (from_base 2) (
    transpose (
      map (to_maxbits k) (
        to_base (2^k) n
      )
    )
  )

from_tuple ns = from_base (2^k) (
    map (from_base 2) (
      transpose (
        map (to_maxbits l) ns
      )
    )
  ) where 
      k=genericLength ns
      l=max_bitcount ns    

type N2 = (N,N)

n2 :: Encoder N2
n2 = compose (Iso pair unpair) nat

hd' = head . nat2ftuple
tl' = ftuple2nat . tail . nat2ftuple
cons' h t  = ftuple2nat (h:(nat2ftuple t))

pair' (x,y) = (cons' x y)-1
unpair' z = (hd' z', tl' z') where z'=z+1

tl'' n = borrow_from nats tail nat n

nat2 :: Encoder (N,N)
nat2 = compose (Iso bitpair bitunpair) nat

bitpair (x,y) = from_tuple [x,y]
bitunpair z = (x,y) where [x,y] = to_tuple 2 z

pairKL k l (x,y) = from_tuple (xs ++ ys) where
   xs = to_tuple k x
   ys = to_tuple l y
   
unpairKL k l z = (x,y) where 
  zs=to_tuple (k+l) z
  xs=genericTake k zs
  ys=genericDrop k zs
  x=from_tuple xs
  y=from_tuple ys

ftuple2nat [] = 0
ftuple2nat ns = succ (pair (pred k,t)) where
  k=genericLength ns 
  t=from_tuple ns

nat2ftuple 0 = []
nat2ftuple kf = to_tuple (succ k) f where 
  (k,f)=unpair (pred kf)

nat :: Encoder N
nat = Iso nat2ftuple ftuple2nat 

data Term var const = 
   Var var | 
   Fun const [Term var const] 
   deriving (Eq,Ord,Show,Read)

type NTerm = Term N N

nterm2code :: Term N N -> N

nterm2code (Var i) = 2*i
nterm2code (Fun cName args) = code where
  cs=map nterm2code args
  fc=as nat nats (cName:cs)
  code = 2*fc-1

code2nterm :: N -> Term N N

code2nterm n | even n = Var (n `div` 2) 
code2nterm n = Fun cName args where
  k = (n+1) `div` 2
  cName:cs = as nats nat k
  args = map code2nterm cs

nterm :: Encoder NTerm
nterm = compose (Iso nterm2code code2nterm) nat

string :: Encoder String
string = compose (Iso string2nat nat2string) nat

base = ord 'z'- ord 'a'
chr2ord c | c>='a' && c<='z' = ord c - ord 'a'

ord2chr o | o>=0 && o<=base = chr (ord 'a'+o)

string2nat cs = from_base 
  (fromIntegral base) 
  (map (fromIntegral . chr2ord) cs)

nat2string n = map 
  (ord2chr . fromIntegral) 
  (to_base (fromIntegral base) n)


type STerm = Term N String

sterm2code :: Term N String -> N

sterm2code (Var i) = 2*i
sterm2code (Fun name args) = code where
  cName=as nat string name
  cs=map sterm2code args
  fc=as nat nats (cName:cs)
  code=2*fc-1

code2sterm :: N -> Term N String

code2sterm n | even n = Var (n `div` 2) 
code2sterm n = Fun name args where
  k = (n+1) `div` 2
  cName:cs = as nats nat k
  name = as string nat cName
  args = map code2sterm cs

sterm :: Encoder STerm
sterm = compose (Iso sterm2code code2sterm) nat

bits :: Encoder [N]
bits = compose (Iso as_nat_bits as_bits_nat) nat

as_bits_nat = drop_last . (to_base 2) . succ where
  drop_last = reverse . tail . reverse

as_nat_bits bs = pred (from_base 2 (bs ++ [1]))

nterm2bits = as bits nterm
bits2nterm = as nterm bits

sterm2bits = as bits sterm
bits2sterm = as sterm bits

xhd :: N->N->N
xhd b n | b>1 && n>0 = 
  if n `mod` b > 0 then 0 else 1+xhd b (n `div` b)

xtl :: N->N->N
xtl b n = y where
  y'= n `div` b^(xhd b n)
  q = y' `div` b
  m = y' `mod` b -- rebase to b
  y = (b-1)*q+m-1

xcons :: N->N->N->N
xcons b x y  | b>1 = (b^x)*y' where
   q =  y `div` (b-1)
   m = y `mod` (b-1) -- rebase to b-1
   y' = b*q + (m+1)

xunpair b n = (xhd b n',xtl b n') where n'=n+1

xpair b (x,y) = (xcons b x y)-1

nat2pmset 0 = []
nat2pmset n = 
  map (to_pos_in (h:ts)) (to_factors (n+1) h ts) where
      (h:ts)=genericTake (n+1) primes

pmset2nat [] = 0
pmset2nat ns = (product ks)-1 where
  ks=map (from_pos_in ps) ns
  ps=primes
  from_pos_in xs n = xs !! (fromIntegral n)

pmset :: Encoder [N]
pmset = compose (Iso pmset2nat nat2pmset) nat

nats2goedel ns =  product xs where
  xs=zipWith (^) primes ns

goedel2nats n = combine ds xs where
  pss=group (to_primes n)
  ps=map head pss
  xs=map genericLength pss
  ds=as nats set (map pi' ps)
  
  combine [] [] = []
  combine (b:bs) (x:xs) = 
    replicate (fromIntegral b) 0 ++ x:(combine bs xs)

goedel :: Encoder [N]
goedel = compose (Iso nats2g g2nats) nat

nats2g [] = 0
nats2g ns = pred (nats2goedel (z:ns)) where
  z=countZeros (reverse ns)

g2nats 0 = []  
g2nats n = ns ++ (replicate (fromIntegral z) 0) where 
  (z:ns)=goedel2nats (succ n)
    
countZeros (0:ns) = 1+countZeros ns
countZeros _ = 0

goedel' :: Encoder [N]
goedel' = compose (Iso nats2gnat gnat2nats) nat

nats2gnat = pmset2nat . as_mset_nats

gnat2nats = as_nats_mset . nat2pmset

mprod _ 0 _ = 0
mprod _ _ 0 = 0
mprod msetEncoder n m = mshift 
  (borrow_from2 msetEncoder sconcat nat) n m

mshift f x y = 1+(f (x-1) (y-1))
sconcat xs ys = sort (xs ++ ys)

mexp _ n 0 = 1
mexp msetEncoder n k = 
  mprod msetEncoder n (mexp msetEncoder n (k-1))

mgcd msetEncoder x y = mshift 
  (borrow_from2 msetEncoder msetInter nat) x y

mlcm msetEncoder x y = mshift 
  (borrow_from2 msetEncoder msetUnion nat) x y

mDif msetEncoder x y = mshift 
  (borrow_from2 msetEncoder msetDif nat) x y

mSymDif msetEncoder x y = mshift 
  (borrow_from2 msetEncoder msetSymDif nat) x y

mdivides msetEncoder x y = 
  x==(mgcd msetEncoder x y)


is_mprime msetEncoder p | p<2 = False
is_mprime msetEncoder p  = 
  []==[n|n<-[2..p-1],mdivides msetEncoder n p]

mprimes msetEncoder = 
  filter (is_mprime msetEncoder) [2..]

z:: Encoder Z
z = compose (Iso z2nat nat2z) nat

nat2z n = if even n then n `div` 2 else (-n-1) `div` 2
z2nat n = if n<0 then -2*n-1 else 2*n

type Z = Integer
type Z2 = (Z,Z)

z2 :: Encoder Z2
z2 = compose (Iso zpair zunpair) nat

zpair (x,y) = (nat2z . bitpair) (z2nat x,z2nat y)
zunpair z = (nat2z n,nat2z m) where 
  (n,m)= (bitunpair . z2nat) z

set2sat = map (set2disj . (as set nat)) where
  shift0 z = if (z<0) then z else z+1
  set2disj = map (shift0. nat2z)
  
sat2set = map ((as nat set) . disj2set) where
  shiftback0 z = if(z<0) then z else z-1
  disj2set = map (z2nat . shiftback0)

sat :: Encoder [[Z]]
sat = compose (Iso sat2set set2sat) set

to_elias :: N -> [N]
to_elias n = (to_eliasx (succ n))++[0]

to_eliasx 1 = []
to_eliasx n = xs where
  bs=to_lbits n
  l=(genericLength bs)-1
  xs = if l<2 then bs else (to_eliasx l)++bs

from_elias :: [N] -> (N, [N])
from_elias bs = (pred n,cs) where (n,cs)=from_eliasx 1 bs

from_eliasx n (0:bs) = (n,bs)
from_eliasx n (1:bs) = r where 
  hs=genericTake n bs
  ts=genericDrop n bs
  n'=from_lbits (1:hs)
  r=from_eliasx n' ts 

to_lbits = reverse . (to_base 2)

from_lbits = (from_base 2) . reverse

elias :: Encoder [N]
elias = compose (Iso (fst . from_elias) to_elias) nat

data T = H [T] deriving (Eq,Ord,Read,Show)

unrank :: (a -> [a]) -> a -> T
mapUnrank :: (a -> [a]) -> [a] -> [T]

unrank f n = H (mapUnrank f (f n))
mapUnrank f ns = map (unrank f) ns

rank :: ([b] -> b) -> T -> b
mapRank :: ([b] -> b) -> [T] -> [b]

rank g (H ts) = g (mapRank g ts)
mapRank g ts = map (rank g) ts

lift :: Iso b [b] -> Iso T b
lift (Iso f g) = Iso (rank g) (unrank f)

mapLift :: Iso b [b] -> Iso [T] [b]
mapLift (Iso f g) = Iso (mapRank g) (mapUnrank f)

hfs :: Encoder T
hfs=compose (lift (Iso (as set nat) (as nat set))) nat

ackermann = as nat hfs
inverse_ackermann = as hfs nat

hff :: Encoder T
hff = compose (lift nat) nat

hfm :: Encoder T

hfm=compose (lift (Iso (as mset nat) (as nat mset))) nat

hff_pars :: Encoder [N]
hff_pars = compose (Iso pars2hff hff2pars) hff

pars2hff cs = parse_pars 0 1 cs

parse_pars l r cs | newcs == [] = t where
  (t,newcs)=pars_expr l r cs

pars_expr l r (c:cs) | c==l = ((H ts),newcs) where 
  (ts,newcs) = pars_list l r cs    
  pars_list l r (c:cs) | c==r = ([],cs)
  pars_list l r (c:cs) = ((t:ts),cs2) where 
    (t,cs1)=pars_expr l r (c:cs)
    (ts,cs2)=pars_list l r cs1

hff2pars = collect_pars 0 1

collect_pars l r (H ns) =
  [l] ++ (concatMap (collect_pars l r) ns) ++ [r] 

sparses_to m = [n|n<-[0..m-1],
  (genericLength (as hff_pars nat n)) 
  <
  (genericLength (as elias nat n))]

hff_bitsize n= sum (map size [0..2^n-1]) where
   size k=genericLength (as hff_pars nat k) 
elias_bitsize n= sum (map size [0..2^n-1]) where
   size k=genericLength (as elias nat k)    
bitsize n= sum (map size [0..2^n-1]) where
   size k=genericLength (as bits nat k)    

info_density_hff n = (bitsize n) / (hff_bitsize n)

info_density_elias n = (bitsize n) / (elias_bitsize n)

relative_density_hff n = 
  (elias_bitsize n) / (hff_bitsize n)

nat2sfun n = nat2self (as nats nat) n   

nat2self f n = (to_elias l) ++ concatMap to_elias ns where
  ns = f n
  l=genericLength ns

self2nat g ts = (g xs,ts') where 
  (l,ns) = from_elias ts
  (xs,ts')=take_from_elias l ns

  take_from_elias 0 ns = ([],ns) 
  take_from_elias k ns = ((x:xs),ns'') where
     (x,ns')=from_elias ns
     (xs,ns'')=take_from_elias (k-1) ns'
  
sfun2nat ns = xs where (xs,[])=self2nat (as nat nats) ns

sfun_bitsize n= sum (map size [0..2^n-1]) where
   size k=genericLength (nat2sfun k)   

t0=Fun 0 [Var 0,Var 1]
t1=Fun 1 [t0,t0]
t2=Fun 2 [t0,t0,t1,t1,t1]
t3=Fun 3 [t0,t1,t2]


data Iso a b = Iso (a->b) (b->a)

compose :: Iso a b -> Iso b c -> Iso a c
compose (Iso f g) (Iso f' g') = Iso (f' . f) (g . g')

itself = Iso id id

invert (Iso f g) = Iso g f

type N = Integer
isN n = n>=0

type Encoder a = Iso a [N]

nats :: Encoder [N]
nats = itself

as :: Encoder a -> Encoder b -> b -> a
as that this x = g x where 
   Iso _ g = compose that (invert this)

borrow_from :: Encoder b -> (b -> b) ->
               Encoder a -> a -> a

borrow_from lender f borrower = 
  (as borrower lender) . f . (as lender borrower)

borrow_from2 :: Encoder a -> (a -> a -> a) -> 
                Encoder b -> b -> b -> b

borrow_from2 lender op borrower x y = 
    as borrower lender r where
       x'= as lender borrower x
       y'= as lender borrower y
       r = op x' y'

mset :: Encoder [N]
mset = compose (Iso as_nats_mset as_mset_nats) nats

as_mset_nats ns = tail (scanl (+) 0 ns)
as_nats_mset ms = zipWith (-) (ms) (0:ms)

set :: Encoder [N]
set = compose (Iso as_nats_set as_set_nats) nats

as_set_nats = (map pred) . as_mset_nats . (map succ)
as_nats_set = (map pred) . as_nats_mset . (map succ)

bitcount n = head [x|x<-[1..],(2^x)>n]
max_bitcount ns = foldl max 0 (map bitcount ns)

to_maxbits maxbits n = 
  bs ++ (genericTake (maxbits-l)) (repeat 0) where 
    bs=to_base 2 n
    l=genericLength bs

to_base base n | base > 1 = d : 
  (if q==0 then [] else (to_base base q)) where
     (q,d) = quotRem n base
    
from_base base [] = 0
from_base base (x:xs) | x>=0 && x<base = 
   x+base*(from_base base xs)

primes = 2 : filter is_prime [3,5..]

is_prime p = [p]==to_primes p

to_primes n | n>1 = to_factors n p ps where 
  (p:ps) = primes

to_factors n p ps | p*p > n = [n]
to_factors n p ps | 0==n `mod` p = 
   p : to_factors (n `div` p)  p ps 
to_factors n p ps@(hd:tl) = to_factors n hd tl

pi_ n = primes !! (fromIntegral n)
pi' p | is_prime p= to_pos_in primes p

to_pos_in xs x = 
  fromIntegral i where Just i=elemIndex x xs

msetInter xs ys = sort (msetInter' xs ys)

msetInter' [] _ = []
msetInter' _ [] = []
msetInter' (x:xs) (y:ys) | x==y = 
  (x:zs) where zs=msetInter' xs ys
msetInter' (x:xs) (y:ys) | x<y = msetInter' xs (y:ys)
msetInter' (x:xs) (y:ys) | x>y = msetInter' (x:xs) ys

msetDif xs ys = sort (msetDif' xs ys)

msetDif' [] _ = []
msetDif' xs [] = xs
msetDif' (x:xs) (y:ys) | x==y = zs where 
  zs=msetDif' xs ys
msetDif' (x:xs) (y:ys) | x<y = (x:zs) where 
  zs=msetDif' xs (y:ys)
msetDif' (x:xs) (y:ys) | x>y = zs where 
  zs=msetDif' (x:xs) ys

msetSymDif xs ys = 
  sort ((msetDif xs ys) ++ (msetDif ys xs))

msetUnion xs ys = sort ((msetDif xs ys) ++ 
  (msetInter xs ys) ++ (msetDif ys xs))
  
msetIncl xs ys = xs==msetInter xs ys
 

