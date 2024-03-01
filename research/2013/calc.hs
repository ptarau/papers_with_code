module Calc where
import System.CPUTime

class Eq n => N n where

  e :: n
  o,o',i,i' :: n->n
  o_ :: n->Bool

  e_,i_ :: n->Bool
  e_ x = x == e
  i_ x = not (e_ x || o_ x)

  s,s' :: n->n
  
  s x | e_ x = o x
  s x | o_ x = i (o' x)
  s x | i_ x = o (s (i' x))
  
  s' x | x == o e = e
  s' x | i_ x = o (i' x)
  s' x | o_ x = i (s' (o' x))

  add :: n->n->n
  add x y | e_ x = y
  add x y | e_ y  = x
  add x y | o_ x && o_ y = i (add (o' x) (o' y))
  add x y | o_ x && i_ y = o (s (add (o' x) (i' y)))
  add x y | i_ x && o_ y = o (s (add (i' x) (o' y)))
  add x y | i_ x && i_ y = i (s (add (i' x) (i' y)))
  
  sub :: n->n->n
  sub x y | e_ y = x
  sub y x | o_ y && o_ x = s' (o (sub (o' y) (o' x))) 
  sub y x | o_ y && i_ x = s' (s' (o (sub (o' y) (i' x))))
  sub y x | i_ y && o_ x = o (sub (i' y) (o' x))  
  sub y x | i_ y && i_ x = s' (o (sub (i' y) (i' x))) 

  mul :: n->n->n
  mul x _ | e_ x = e
  mul _ y | e_ y = e
  mul x y = s (m (s' x) (s' y)) where
    m x y | e_ x = y
    m x y | o_ x = o (m (o' x) y)
    m x y | i_ x = s (add y  (o (m (i' x) y)))

  db,hf :: n->n 
  db = s' . o
  hf = o' .s 

  pow :: n->n->n
  pow _ y | e_ y = o e
  pow x y | o_ y = mul x (pow (mul x x) (o' y))
  pow x y | i_ y = mul (mul x x) (pow (mul x x) (i' y)) 

  exp2 :: n->n
  exp2 x | e_ x = o e
  exp2 x = s (fPow o x e) 
  
  leftshiftBy :: n->n->n
  leftshiftBy _ k |e_ k = e
  leftshiftBy n k = s (fPow o n (s' k))
  
  fPow :: (n->n)->n->n->n
  fPow _ n x | e_ n = x
  fPow f n x  = fPow f (s' n) (f x)

instance N Integer where
  e = 0
  
  o_ x = odd x
  
  o  x = 2*x+1
  o' x | odd x && x >  0 = (x-1) `div` 2
  
  i  x = 2*x+2
  i' x | even x && x > 0 = (x-2) `div` 2

data B = B | O B | I B deriving (Show, Read, Eq)

instance N B where
  e = B
  o = O
  i = I
  
  o' (O x) = x
  i' (I x) = x
  
  o_ (O _) = True
  o_ _ = False

data T = T | V T [T] | W T [T] deriving (Eq,Show,Read)

instance N T where
  e = T
  
  o T = V T []
  o (V x xs) = V (s x) xs
  o (W x xs) = V T (x:xs)

  i T = W T []
  i (V x xs) = W T (x:xs)
  i (W x xs) = W (s x) xs
  
  o' (V T []) = T
  o' (V T (x:xs)) = W x xs
  o' (V x xs) = V (s' x) xs

  i' (W T []) = T
  i' (W T (x:xs)) = V x xs
  i' (W x xs) = W (s' x) xs
  
  o_ (V _ _ ) = True
  o_ _ = False

  exp2 T = V T []
  exp2 x = s (V (s' x) [])

  leftshiftBy _ T = T
  leftshiftBy n k = s (otimes n (s' k))

otimes T y = y
otimes n T = V (s' n) []
otimes n (V y ys) = V (add n y) ys
otimes n (W y ys) = V (s' n) (y:ys)

view :: (N a,N b)=>a->b
view x | e_ x = e
view x | o_ x = o (view (o' x))
view x | i_ x = i (view (i' x))

t :: (N n) => n -> T
t = view

b :: (N n) => n -> B
b = view

n :: (N n) => n -> Integer
n = view

fermat n = s (exp2 (exp2 n))

mersenne p = s' (exp2 p)

perfect p = s (V q [q]) where q = s' (s' p)

-- its exponent
prime48 = 57885161 :: Integer

-- the actual Mersenne prime
mersenne48 = s' (exp2 (t p)) where 
  p = prime48::Integer

perfect48 = perfect (t prime48)

prothPrime = s (leftshiftBy n k) where 
  n = t (13018586::Integer)
  k = t (19249::Integer)

twinPrimes = (s' m,s m) where 
  n = t (666669::Integer)
  k = t (3756801695685::Integer)
  m = leftshiftBy n k

class N n => SpecialComputations n where
  dual :: n->n
  dual x | e_ x = e
  dual x | o_ x = i (dual (o' x))
  dual x | i_ x = o (dual (i' x))

  bitsize :: n->n
  bitsize x | e_ x = e
  bitsize x | o_ x = s (bitsize (o' x))
  bitsize x | i_ x = s (bitsize (i' x))

  repsize :: n->n
  repsize = bitsize

instance SpecialComputations Integer
instance SpecialComputations B
instance SpecialComputations T where
  bitsize T = T
  bitsize (V x xs) = s (foldr add1 x xs) where add1 x y = s (add x y)
  bitsize (W x xs) = s (foldr add1 x xs) where add1 x y = s (add x y)
    
  dual T = T
  dual (V x xs) = W x xs
  dual (W x xs) = V x xs 
    
  repsize T = T
  repsize (V x xs) = s (foldr add T (map repsize (x:xs)))
  repsize (W x xs) = s (foldr add T (map repsize (x:xs)))

