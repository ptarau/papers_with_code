module NSF10 where
import Data.Bits

type N = Integer

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

data Iso a b = Iso (a->b) (b->a)

compose :: Iso a b -> Iso b c -> Iso a c
compose (Iso f g) (Iso f' g') = Iso (f' . f) (g . g')

itself = Iso id id

invert (Iso f g) = Iso g f

type Encoder a = Iso a N

nat :: Encoder N
nat = itself

nats :: Encoder [N] 
nats = Iso as_nat_nats as_nats_nat

as :: Encoder a -> Encoder b -> b -> a
as (Iso _ toB) (Iso fromA _) = toB . fromA      

class (Eq n,Read n,Show n)=>SharedAxioms n where  
  e :: n 
  o_ :: n->Bool
  o,i,r :: n->n 

  e_,i_ :: n->Bool
  e_ x = x==e
  i_ x = not (o_ x || e_ x)

  u :: n
  u = o e
  
  u_ :: n->Bool
  u_ x = o_ x && e_ (r x)

  s,p :: n->n 
  
  s x | e_ x = u
  s x | o_ x = i (r x)
  s x | i_ x = o (s (r x)) 
  
  p x | u_ x = e
  p x | o_ x = i (p (r x)) 
  p x | i_ x = o (r x)

view :: (SharedAxioms a,SharedAxioms b)=>a->b
view x | e_ x = e
view x | o_ x = o (view (r x))
view x | i_ x = i (view (r x))

allFrom k = k : allFrom (s k)

instance SharedAxioms Integer where
  e = 0
  o_ x = odd x
  o x = 2*x+1
  i x = 2*x+2
  r x | x/=0 =(x-1) `div` 2

class (SharedAxioms n) => SharedArithmetic n where
  a,d :: n->n->n 
  
  a x y | e_ x = y
  a x y | e_ y = x
  a x y | o_ x && o_ y =    i (a (r x) (r y))
  a x y | o_ x && i_ y = o (s (a (r x) (r y)))
  a x y | i_ x && o_ y = o (s (a (r x) (r y)))
  a x y | i_ x && i_ y = i (s (a (r x) (r y)))
  
  d x y | e_ x && e_ y = e
  d x y | not(e_ x) && e_ y = x
  d x y | not (e_ x) && x==y = e
  d z x | i_ z && o_ x = o (d (r z) (r x))  
  d z x | o_ z && o_ x = i (d (r z) (s (r x)))  
  d z x | o_ z && i_ x = o (d (r z) (s (r x)))
  d z x | i_ z && i_ x = i (d (r z) (s (r x)))  

  m :: n->n->n
  
  m x _ | e_ x = e
  m _ y | e_ y = e
  m x y = s (m0 (p x) (p y)) where
    m0 x y | e_ x = y
    m0 x y | o_ x = o (m0 (r x) y)
    m0 x y | i_ x = s (a y  (o (m0 (r x) y)))

instance SharedArithmetic Integer

infixr 5 :->

data T = T | T :-> T deriving (Eq, Read, Show)

instance SharedAxioms T where
  e = T
 
  o_ (T:->_) = True
  o_ x = False
 
  o x = T :-> x
 
  i = s . o

  r (T:->y) = y
  r (x:->y) = p (p x:->y) 

  s T = T:->T
  s (T:->y) = s x:->y' where x:->y' = s y
  s (x:->y) = T:->(p x:->y) 
 
  p (T:->T) = T
  p (T:->(x:->y)) = s x:->y
  p (x:->y) = T:->p (p x:->y)

instance SharedArithmetic T

t_pair (x,y) = 1 + (cons x y)
t_unpair z = (hd z', tl z') where z'=z-1 

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

nat2gray, gray2nat :: N->N

nat2gray n= n `xor` (shiftR n 1)

gray2nat 0 = 0
gray2nat n = ((firstBit n) `xor` (firstBit n')) .|. (twice n') where n'=gray2nat (half n)

gray_bitpair (x,y) = gray2nat (bitpair (nat2gray x,nat2gray y))
gray_bitunpair z = (gray2nat x,gray2nat y) where 
  (x,y)=bitunpair (nat2gray z)

