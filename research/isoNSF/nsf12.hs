module NSF12 where
import Data.Bits

type N = Integer

cons :: N->N->N
cons x y  = (2^x)*(2*y+1)

hd :: N->N
hd n | n>0 = if odd n then 0 else 1+hd  (n `div` 2)

tl :: N->N
tl n | n>0 = if odd n then (n-1) `div` 2 else tl (n `div` 2)

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

class (Read n,Show n)=>PureTypes n where  
  e :: n
  c :: n->n->n
  l,r :: n->n
  e_ :: n->Bool 

  c_ :: n->Bool
  c_ = not . e_
  
  eq :: n -> n -> Bool
  eq x y | e_ x = e_ y
  eq x y = eq (l x) (l y) && eq (r x) (r y)

  like :: (PureTypes m)=>m->n->m
  like _ a = view a where
     view x | e_ x = e
     view x = c (view (l x)) (view (r x))

infixr 5 :->
data T = E|T :-> T deriving (Read, Show)

instance PureTypes T where
  e = E
  c = (:->)
  l (x :-> _) = x
  r (_ :-> y) = y

  e_ E = True
  e_ _ = False

asT x = like E x

instance PureTypes Integer where
  e=0
  c x y = cons x y
  l x = hd x
  r x = tl x
 
  e_ 0 = True
  e_ _ = False

asN x = like 0 x

class PureTypes n=>PeanoArith n where 
  s,p :: n->n
   
  s x | e_ x = c e e
  s x | e_ (l x) = c (s (l (s (r x)))) (r (s (r x)))
  s x = c e (c (p (l x)) (r x))      
   
  p x | e_ (l x) && e_ (r x) = e
  p x | e_ (l x) = c (s (l (r x))) (r (r x))
  p x = c e (p (c (p (l x)) (r x)))  
  
instance PeanoArith T 
instance PeanoArith Integer

allFrom k = k : allFrom (s k)

class PeanoArith n=>FastArith n where
  o_,i_ :: n->Bool
  o_ x = c_ x && e_ (l x)
  i_ x = c_ x && c_ (l x)

  o,i :: n->n
  o x = c e x
  i = s . o

  o',i' :: n->n 
  o' x | e_ (l x) = r x 
  i' x | c_ (l x) = p (c (p (l x)) (r x)) 

  add :: n->n->n
  
  add x y | e_ x = y
  add x y | e_ y = x
  add x y | o_ x && o_ y = i (add (o' x) (o' y))
  add x y | o_ x && i_ y = o (s (add (o' x) (i' y)))
  add x y | i_ x && o_ y = o (s (add (i' x) (o' y)))
  add x y | i_ x && i_ y = i (s (add (i' x) (i' y)))

  sub :: n->n->n
  sub x y | e_ y = x
  sub y x | o_ y && o_ x = p (o (sub (o' y) (o' x))) 
  sub y x | o_ y && i_ x = p (p (o (sub (o' y) (i' x))))
  sub y x | i_ y && o_ x = o (sub (i' y) (o' x))  
  sub y x | i_ y && i_ x = p (o (sub (i' y) (i' x)))  

  half,double,exp2 :: n->n
  
  double = p . o
  half x = if o_ x' then o' x' else i' x' where x'=s x
  exp2 x = c x e

  multiply, pow :: n->n->n
  
  multiply x _ |e_ x = e
  multiply _ x |e_ x = e   
  multiply x y = c (add (l x) (l y)) (add a m) where
    (x',y')=(r x,r y)
    a=add x' y'
    m=double (multiply x' y')

  pow _ y | e_ y = c e e
  pow x y | o_ y = multiply x (pow (multiply x x) (o' y))
  pow x y | i_ y = multiply x' (pow x' (i' y)) where x'=multiply x x

instance FastArith Integer
instance FastArith T

-- N -> Q+ by navigating the Calkin-Wilf tree starting from its root
n2q 0 = (1,1)
n2q x | odd x =  (f0,f0+f1) where 
  (f0,f1) = n2q (div (pred x) 2) 
n2q x | even x  = (f0+f1,f1) 
  where (f0,f1)=n2q (pred (div x 2))

-- Q+ -> N, fast, by navigating the Calkin-Wilf tree backwards
q2n (1,1) = 0
q2n (a,b) = f (compare a b) where 
  f LT = 2*(q2n (a,b-a))+1
  f GT = 2*(q2n (a-b,b))+2

