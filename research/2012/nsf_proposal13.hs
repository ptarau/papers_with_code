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
  s' x | o_ x = i (s' (o' x))
  s' x | i_ x = o (i' x)  

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

  cmp :: n->n->Ordering
  cmp x y | e_ x && e_ y = EQ
  cmp x _ | e_ x = LT
  cmp _ y | e_ y = GT
  cmp x y | o_ x && o_ y = cmp (o' x) (o' y)
  cmp x y | i_ x && i_ y = cmp (i' x) (i' y)
  cmp x y | o_ x && i_ y = down (cmp (o' x) (i' y)) where
    down EQ = LT
    down r = r
  cmp x y | i_ x && o_ y = up (cmp (i' x) (o' y)) where
    up EQ = GT
    up r = r

  mul :: n->n->n
  mul x _ | e_ x = e
  mul _ y | e_ y = e
  mul x y = s (m (s' x) (s' y)) where
    m x y | e_ x = y
    m x y | o_ x = o (m (o' x) y)
    m x y | i_ x = s (add y  (o (m (i' x) y)))

  db :: n->n 
  db = s' . o
  
  hf :: n->n
  hf = s.i'

  pow :: n->n->n
  pow _ y | e_ y = o e
  pow x y | o_ y = mul x (pow (mul x x) (o' y))
  pow x y | i_ y = mul 
    (mul x x) 
    (pow (mul x x) (i' y)) 

  exp2 :: n->n
  exp2 x | e_ x = o e
  exp2 x = db (exp2 (s' x)) 
  
  leftshift :: n->n->n
  leftshift x y = mul (exp2 x) y

  div_and_rem :: n->n->(n,n)
  
  div_and_rem x y | LT == cmp x y = (e,x)
  div_and_rem x y | not (e_ y) = (q,r) where 
    (qt,rm) = divstep x y
    (z,r) = div_and_rem rm y
    q = add (exp2 qt) z
    
    divstep n m = (q, sub n p) where
      q = try_to_double n m e
      p = mul (exp2 q) m    
    
      try_to_double x y k | LT==cmp x y = s' k
      try_to_double x y k = 
        try_to_double x (db y) (s k)   
          
  divide,reminder :: n->n->n
  
  divide n m = fst (div_and_rem n m)
  reminder n m = snd (div_and_rem n m)

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
  
  o_ (O _) = True
  o_ _ = False
  
  o' (O x) = x
  i' (I x) = x

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

  exp2 = exp2' where
    exp2' T = V T []
    exp2' x = s (V (s' x) [])

  leftshift = leftshift' where
   leftshift' _ T = T
   leftshift' n y | o_ y = s (vmul n (s' y))
   leftshift' n y | i_ y = s (vmul (s n) (s' y))

vmul T y = y
vmul n T = V (s' n) []
vmul n (V y ys) = V (add (s' n) y) ys
vmul n (W y ys) = V (s' n) (y:ys)

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
prime45 = 43112609

-- the actual Mersenne prime
mersenne45 = s' (exp2 (t p)) where 
  p = prime45::Integer


perfect45 = perfect (t prime45)

class N n => SpecialComputations n where
 -- dual in bijective base 2, obtained by
 
  -- flipping Os with Is  
  dual :: n->n
  dual x | e_ x = e
  dual x | o_ x = i (dual (o' x))
  dual x | i_ x = o (dual (i' x))
    
  -- bitsize of a number in bijective base 2
  bitsize :: n->n
  bitsize x | e_ x = e
  bitsize x | o_ x = s (bitsize (o' x))
  bitsize x | i_ x = s (bitsize (i' x))

instance SpecialComputations Integer
instance SpecialComputations B
instance SpecialComputations T where
  bitsize = tbitsize where
    tbitsize T = T
    tbitsize (V x xs) = s (foldr add1 x xs)
    tbitsize (W x xs) = s (foldr add1 x xs)
    
    add1 x y = s (add x y)
    
  dual = tdual where
    tdual T = T
    tdual (V x xs) = W x xs
    tdual (W x xs) = V x xs 

class (N n) => Collections n where

  c :: n->n->n
  c' :: n->n
  c'' :: n->n
  
  c' x | not (e_ x) = if o_ x then e else s (c'  (hf x))
  c'' x | not (e_ x) = if o_ x then o' x else c'' (hf x)

  c x y = mul (exp2 x) (o y)

  to_list,to_mset,to_set :: n->[n]
  from_list,from_mset,from_set :: [n]->n
  list2mset, mset2list, list2set, set2list :: [n]->[n]
  
  to_list x | e_ x = []
  to_list x = (c' x) : (to_list (c'' x))

  from_list [] = e
  from_list (x:xs) = c x (from_list xs)

  list2mset ns = tail (scanl add e ns)
  mset2list ms =  zipWith sub ms (e:ms)
    
  list2set = (map s') . list2mset . (map s)
  set2list = (map s') . mset2list . (map s) 


  to_mset = list2mset . to_list
  from_mset = from_list . mset2list
  
  to_set = list2set . to_list
  from_set = from_list . set2list

instance Collections B
instance Collections Integer
instance Collections T where
  c = tcons where
    tcons n y = s (vmul n (s' (o y)))

ack x n | e_ x = s n
ack m1 x | e_ x = ack (s' m1) (s e)
ack m1 n1 = ack (s' m1) (ack m1 (s' n1))

bm1t = benchmark "ack 3 7 on t" (ack (t (toInteger 3)) (t (toInteger 7)))
bm1b = benchmark "ack 3 7 on t" (ack (b (toInteger 3)) (b (toInteger 7)))
bm1n = benchmark "ack 3 7 on t" (ack (n (toInteger 3)) (n (toInteger 7)))

bm2t = benchmark "exp2 t" (exp2 (exp2 (t (toInteger 14))))
bm2b = benchmark "exp2 b" (exp2 (exp2 (b (toInteger 14))))
bm2n = benchmark "exp2 n" (exp2 (exp2 (n (toInteger 14))))

bm3 tvar = benchmark "sparse_set on a type" (n (bitsize (from_set ps)))
  where ps = map tvar [101,2002..100000]

bm4t =benchmark "bitsize of Mersenne 45"  (n (bitsize mersenne45))
bm5t = benchmark "bitsize of Perfect 45" ( n (bitsize perfect45))

bm6t = benchmark "large leftshift" (leftshift n n) where
  n = t prime45

benchmark mes f = do
  x<-getCPUTime
  print f
  y<-getCPUTime
  let time=(y-x) `div` 1000000000
  return (mes++" :time="++(show time))


