module Goedel where
import Data.List
import Data.Bits
import Data.Char

cons :: N->N->N
cons x y  = shiftL (1 .|. (shiftL y 1)) (fromIntegral x)

hd :: N->N
hd n | n>0 = if 1==n .&. 1 then 0 else succ (hd  (shiftR n 1))

tl :: N->N
tl n = shiftR n (fromIntegral (succ (hd n)))

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

type N2 = (N,N)

n2 :: Encoder N2
n2 = compose (Iso pair unpair) nat

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

bijnat :: N->Encoder [N]

bijnat a = compose (Iso (from_bbase a) (to_bbase a)) nat

from_bbase base xs = from_base' base (map succ xs)

from_base' base [] = 0
from_base' base (x:xs) | x>0 && x<=base = 
   x+base*(from_base' base xs)
   
to_bbase base n = map pred (to_base' base n)

to_base' _ 0 = []
to_base' base n = d' : ds where
   (q,d) = quotRem n base
   d'=if d==0 then base else d
   q'=if d==0 then q-1 else q
   ds=if q'==0 then [] else to_base' base q'

c0='a'
c1='z'

base = 1+ord c1-ord c0

string2nat cs = from_bbase (fromIntegral base) 
  (map (fromIntegral . chr2ord) cs)

nat2string n = map (ord2chr . fromIntegral) 
  (to_bbase (fromIntegral base) n)
  
chr2ord c | c>=c0 && c<=c1 = ord c - ord c0
ord2chr o | o>=0 && o<base = chr (ord c0+o)

string :: Encoder String
string = compose (Iso string2nat nat2string) nat

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
bits = bijnat 2 

nterm2bits = as bits nterm
bits2nterm = as nterm bits

sterm2bits = as bits sterm
bits2sterm = as sterm bits

nat2pmset 0 = []
nat2pmset n = map (to_pos_in (h:ts)) (to_factors (n+1) h ts) where
  (h:ts)=genericTake (n+1) primes

pmset2nat [] = 0
pmset2nat ns = (product ks)-1 where
  ks=map (from_pos_in ps) ns
  ps=primes
  from_pos_in xs n = xs !! (fromIntegral n)

pmset :: Encoder [N]
pmset = compose (Iso pmset2nat nat2pmset) nat

pnats :: Encoder [N]
pnats = compose (Iso as_mset_nats as_nats_mset) pmset

pset :: Encoder [N]
pset = compose (Iso as_nats_set as_set_nats) pnats

nats2goedel ns =  product xs where
  xs=zipWith (^) primes ns

goedel2nats n = combine ds xs where
  pss=group (to_primes n)
  ps=map head pss
  xs=map genericLength pss
  ds=as nats set (map pi' ps)
  
  combine [] [] = []
  combine (b:bs) (x:xs) = replicate (fromIntegral b) 0 ++ x:(combine bs xs)

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

to_primes n | n>1 = to_factors n p ps where (p:ps) = primes

to_factors n p ps | p*p > n = [n]
to_factors n p ps | 0==n `mod` p = 
   p : to_factors (n `div` p)  p ps 
to_factors n p (hd:tl) = to_factors n hd tl

pi_ n = primes !! (fromIntegral n)
pi' p | is_prime p= to_pos_in primes p

to_pos_in xs x = 
  fromIntegral i where Just i=elemIndex x xs

-- tests

t1 = as nterm nat 119

