module SharedAxioms where
import Data.List
import Data.Bits
import CPUTime

class (Eq n,Read n,Show n)=>Polymath n where  
  e :: n 
  o_ :: n->Bool
  o :: n->n 
  i :: n->n
  r :: n->n

  e_ :: n->Bool
  e_ x = x==e

  i_ :: n->Bool
  i_ x = not (o_ x || e_ x)

  u :: n
  u = o e
  
  u_ :: n->Bool
  u_ x = o_ x && e_ (r x)

  s :: n->n 
  s x | e_ x = u
  s x | o_ x = i (r x)
  s x | i_ x = o (s (r x)) 
  
  p :: n->n 
  p x | u_ x = e
  p x | o_ x = i (p (r x)) 
  p x | i_ x = o (r x)

view :: (Polymath a,Polymath b)=>a->b
view x | e_ x = e
view x | o_ x = o (view (r x))
view x | i_ x = i (view (r x))

newtype N = N Integer deriving (Eq,Show,Read)
instance Polymath N where
  e = N 0
  o_ (N x) = odd x
  o (N x) = N (2*x+1)
  i (N x) = N (2*x+2)
  r (N x) | x/=0 = N ((x-1) `div` 2)

data Peano = Zero|Succ Peano deriving (Eq,Show,Read)

instance Polymath Peano where
  e = Zero
  
  o_ Zero = False
  o_ (Succ x) = not (o_ x) 
  
  o x = Succ (o' x) where
    o' Zero = Zero
    o' (Succ x) = Succ (Succ (o' x))
    
  i x = Succ (o x)
  
  r (Succ Zero) = Zero
  r (Succ (Succ Zero)) = Zero
  r (Succ (Succ x)) = Succ (r x) 

data S=S [S] deriving (Eq,Read,Show)

instance Polymath S where
  e = S []
  
  o_ (S (S []:_)) = True
  o_ _ = False
  
  o (S xs) = s (S (map s xs))
  
  i = s . o

  s (S xs) = S (hLift (S []) xs) where
    hLift k [] = [k]
    hLift k (x:xs) | k==x = hLift (s x) xs
    hLift k xs = k:xs

  p (S xs) = S (hUnLift xs) where
    hUnLift ((S []):xs) = xs
    hUnLift (k:xs) = hUnLift (k':k':xs) where k'= p k 
    
  r (S xs) = S (map p (f ys)) where 
    S ys = p (S xs)
    f (x:xs) | e_ x = xs
    f xs = xs

data F = F [F] deriving (Eq,Read,Show)

instance Polymath F where 
  e= F []
  
  o_ (F (F []:_))=True
  o_ _ = False
  
  o (F xs) = F (e:xs)

  i (F xs) = s (F (e:xs))

  r (F (x:xs)) | e_ x = F xs
  r (F (k:xs)) = F (hpad (p k) (hnext xs)) where
    hpad x xs | e_ x = xs
    hpad x xs = e : (hpad (p x) xs)
  
    hnext [] = []
    hnext (k:xs) = (s k):xs
  
  s (F xs) = F (hinc xs) where
    hinc ([]) = [e]
    hinc (x:xs) | e_ x= (s k):ys where (k:ys)=hinc xs 
    hinc (k:xs) = e:(p k):xs

  p (F xs) = F (hdec xs) where
    hdec [x] | e_ x= []
    hdec (x:k:xs) | e_ x= (s k):xs
    hdec (k:xs) = e:(hdec ((p k):xs))

class (Polymath n) => Polymath1 n where
  a :: n->n->n 
  a x y | e_ x = y
  a x y | e_ y = x
  a x y | o_ x && o_ y =    i (a (r x) (r y))
  a x y | o_ x && i_ y = o (s (a (r x) (r y)))
  a x y | i_ x && o_ y = o (s (a (r x) (r y)))
  a x y | i_ x && i_ y = i (s (a (r x) (r y)))
  
  d :: n->n->n
  d x y | e_ x && e_ y = e
  d x y | not(e_ x) && e_ y = x
  d x y | not (e_ x) && x==y = e
  d z x | i_ z && o_ x = o (d (r z) (r x))  
  d z x | o_ z && o_ x = i (d (r z) (s (r x)))  
  d z x | o_ z && i_ x = o (d (r z) (s (r x)))
  d z x | i_ z && i_ x = i (d (r z) (s (r x)))  

  lcmp :: n->n->Ordering
  
  lcmp x y | e_ x && e_ y = EQ 
  lcmp x y | e_ x && not(e_ y) = LT
  lcmp x y | not(e_ x) && e_ y = GT
  lcmp x y = lcmp (r x) (r y)

  cmp :: n->n->Ordering
   
  cmp x y = ecmp (lcmp x y) x y where
     ecmp EQ x y = samelen_cmp x y
     ecmp b _ _ = b
     
  samelen_cmp :: n->n->Ordering

  samelen_cmp x y | e_ x && e_ y = EQ
  samelen_cmp x y | e_ x && not(e_ y) = LT
  samelen_cmp x y | not(e_ x) && e_ y = GT
  samelen_cmp x y | o_ x && o_ y = samelen_cmp (r x) (r y)
  samelen_cmp x y | i_ x && i_ y = samelen_cmp (r x) (r y)
  samelen_cmp x y | o_ x && i_ y = 
    downeq (samelen_cmp (r x) (r y)) where
      downeq EQ = LT
      downeq b = b
  samelen_cmp x y | i_ x && o_ y = 
    upeq (samelen_cmp (r x) (r y)) where
      upeq EQ = GT
      upeq b = b

  lt :: n->n->Bool
  lt x y = LT==cmp x y
  
  gt :: n->n->Bool
  gt x y = GT==cmp x y
  
  eq:: n->n->Bool
  eq x y = EQ==cmp x y

  nsort :: [n]->[n]
  nsort ns = sortBy ncompare ns
  
  ncompare :: n->n->Ordering
  ncompare x y | x==y = EQ
  ncompare x y | lt x y = LT
  ncompare _ _ = GT

instance Polymath1 N
instance Polymath1 Peano
instance Polymath1 S
instance Polymath1 F

class (Polymath1 n) => Polymath2 n where
  m :: n->n->n  -- multiplication
  m x _ | e_ x = e
  m _ y | e_ y = e
  m x y = s (m0 (p x) (p y)) where
    m0 x y | e_ x = y
    m0 x y | o_ x = o (m0 (r x) y)
    m0 x y | i_ x = s (a y  (o (m0 (r x) y)))
  
  db :: n->n -- double
  db = p . o
  
  hf :: n->n -- half
  hf = r . s

  exp2 :: n->n -- power of 2
  
  exp2 x | e_ x = u
  exp2 x = db (exp2 (p x)) 

  pow :: n->n->n -- power y of x
  pow _ y | e_ y = u
  pow x y | o_ y = m x (pow2 x y)
  pow x y | i_ y = m (m x x) (pow2 x y) 
   
  pow2 :: n->n->n
  pow2 x y = pow (m x x) (r y) 

instance Polymath2 N
instance Polymath2 Peano
instance Polymath2 S
instance Polymath2 F

infixr 5 :->

data T=T|T :-> T deriving (Eq, Read, Show)

instance Polymath T where
  e = T
 
  o_ (T:->x) = True
  o_ x = False
 
  o x = T :-> x
 
  i x = s (T :-> x)

  r (T:->y) = y
  r (x:->y) = hpad (p x) y where
   
    hpad T y = hnext y
    hpad x y = T:->hpad (p x) y
   
    hnext T = T
    hnext (x:->y) = s x:->y 

  s T = T:->T
  s (T:->y) = s x:->y' where x:->y' = s y
  s (x:->y) = T:->(p x:->y) 
 
  p (T:->T) = T
  p (T:->(x:->y)) = s x:->y
  p (x:->y) = T:->p (p x:->y)

instance Polymath1 T
instance Polymath2 T

