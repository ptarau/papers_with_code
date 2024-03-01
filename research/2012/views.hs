module Views where

data BWrapper n = B | O n | I n deriving (Eq, Show, Read)

class (Read n,Show n,Eq n) => Bins n where  
  b :: n
  
  b_,o_,i_ :: n->Bool
  b_ x = x==b
  
  o,i,o',i' :: n->n
 
  unapply :: n -> BWrapper n
  unapply x | b_ x  = B
  unapply x | o_ x =  O (o' x)
  unapply x | i_ x = I (i' x)    

  apply :: BWrapper n -> n
  apply B = b
  apply (O x) = o x
  apply (I x) = i x
  
class (Bins n) =>  Arith n where 
  s,s' :: n -> n 
  s (unapply->B) = apply (O (apply B))
  s (unapply->O x) = apply (I x)
  s (unapply->I x) = apply (O (s x)) 
  
  s' (unapply->O (unapply->B)) = apply B
  s' (unapply->O x) = apply (I (s' x)) 
  s' (unapply->I x) = apply (O x)

  add:: n->n->n
  add (unapply->B) y = y
  add x (unapply->B) = x
  add (unapply->O x) (unapply->O y) = apply (I (add x y))
  add (unapply->O x) (unapply->I y) = apply (O (s (add x y)))
  add (unapply->I x) (unapply->O y) = apply (O (s (add x y)))
  add (unapply->I x) (unapply->I y) = apply (I (s (add x y)))

  mul :: n->n->n
  mul (unapply->B) _ = apply B
  mul _ (unapply->B) =  apply B
  mul x y = s (m (s' x) (s' y)) where
    m (unapply->B) y = y
    m (unapply->O x) y = apply (O (m x y))
    m (unapply->I x) y = s (add y  (apply (O (m x y))))

instance Bins Integer where
  b=0
  
  o x = 2*x+1
  i x = 2*x+2
  
  o_ x = x>0 && odd x 
  i_ x = x>0 && even x

  o' x = (x-1) `div` 2
  i' x = (x-2) `div` 2
instance Arith Integer

instance Bins [Bool] where
  b=[]
      
  o xs=  False:xs
  i xs = True:xs
  
  o_ (False:_) = True
  o_ _ = False
 
  i_ (True:_) = True
  i_ _ = False
 
  o' (False:xs) = xs
  i' (True:xs) = xs
instance Arith [Bool]

allFrom k = k : allFrom (s k)


data T = T | C T T deriving  (Eq, Show, Read)

sT T = C T T         
sT (C T y) = dT (sT y)  
sT z = C T (dT' z) 

sT' (C T T) = T 
sT' (C T y) = dT y
sT' z = C T (sT' (dT' z))

dT (C a b) = C (sT a) b
dT' (C a b) = C (sT' a) b

instance Bins T where
  b=T
  o = C T
  o' (C T y) = y
  o_ (C x _) = x == T

  i = sT . o
  i' = o' . sT'
  i_ (C x _) = x /= T
  
instance Arith T

data B' = B' | O' B' | I' B'  deriving  (Eq, Show, Read)


instance Bins B' where

  b=B'
  
  o = O'
  i = I'
  
  o_ (O' _) = True
  o_ _ = False
  
  i_ (I' _) = True
  i_ _ = False

  o' (O' x) = x
  
  i' (I' x) = x

instance Arith B'


view (unapply->B) = apply B
view (unapply->O x) = apply (O (view x))
view (unapply->I x) = apply (I (view x))