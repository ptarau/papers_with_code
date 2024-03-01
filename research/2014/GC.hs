module GC where
-- import Visuals

data T = E | C T T deriving (Eq,Show,Read)

data M = F [M] deriving (Eq,Show,Read)

class (Show a,Read a,Eq a) => Cat a where
  e :: a
  
  c :: (a,a) -> a
  c' :: a -> (a,a) 

  e_ :: a -> Bool  
  e_ a = a == e
  
  c_ :: a -> Bool
  c_ a = a /= e

instance Cat T where
  e = E
  
  c (x,y) = C x y 
  
  c' (C x y) = (x,y)

instance Cat M where
  e = F []
  c (x,F xs) = F (x:xs)
  c' (F (x:xs)) = (x,F xs)

type N = Integer
instance Cat Integer where
  e = 0

  c (i,j) | i>=0 && j>=0 = 2^(i+1)*(j+d)-d where 
    d = mod (j+1) 2

  c' k | k>0 = (max 0 (i-1),j-b) where
    b = mod k 2
    (i,j) = dyadicVal (k+b)
  
    dyadicVal k | even k = (1+i,j) where  (i,j) = dyadicVal (div k 2)
    dyadicVal k = (0,k)  

view :: (Cat a, Cat b) => a -> b
view z | e_ z = e
view z | c_ z = c (view x,view y) where (x,y) = c' z

n :: Cat a => a->N
n = view

t :: Cat a => a->T
t = view

m :: Cat a => a->M
m = view

to_list :: Cat a => a -> [a]
to_list x | e_ x = []
to_list x | c_ x  = h:hs where 
    (h,t) = c' x
    hs = to_list t

from_list :: Cat a => [a] -> a
from_list [] = e
from_list (x:xs) = c (x,from_list xs)

catShow :: Cat a => a -> [Char]
catShow x | e_ x = "()"
catShow x | c_ x = r where
    xs = to_list x
    r = "(" ++ (concatMap catShow xs) ++ ")"

even_ :: Cat a => a -> Bool
even_ x | e_ x = True
even_ z | c_ z = odd_ y where (_,y)=c' z

odd_ :: Cat a => a -> Bool
odd_ x | e_ x = False
odd_ z | c_ z = even_ y where (_,y)=c' z

u :: Cat a => a
u = c (e,e)

u_ :: Cat a => a-> Bool
u_ z = c_ z && e_ x && e_ y where (x,y) = c' z

s :: Cat a => a -> a 
s x | e_ x = u -- 1
s z | c_ z && e_ y = c (x,u) where -- 2
   (x,y) = c' z

s a | c_ a = if even_ a then f a else g a where

   f k | c_ w && e_ v = c (s x,y) where -- 3
    (v,w) = c' k
    (x,y) = c' w
   f k = c (e, c (s' x,y)) where -- 4
     (x,y) = c' k     
     
   g k | c_ w && c_ n && e_ m = c (x, c (s y,z)) where -- 5
    (x,w) = c' k
    (m,n) = c' w
    (y,z) = c' n  
   g k | c_ v = c (x, c (e, c (s' y, z))) where -- 6
    (x,v) = c' k
    (y,z) = c' v

s' :: Cat a => a -> a
s' k | u_ k = e where -- 1
    (x,y) = c' k  
s' k | c_ k && u_ v = c (x,e) where -- 2
    (x,v) = c' k 

s' a | c_ a = if even_ a then g' a else f' a where

     g' k | c_ v && c_ w && e_ r = 
                            c (x, c (s y,z)) where -- 6
       (x,v) = c' k
       (r,w) = c' v
       (y,z) = c' w    
     g' k  | c_ v = c (x,c (e, c (s' y, z))) where -- 5
       (x,v) = c' k
       (y,z) = c' v     
       
     f' k | c_ v && e_ r = c (s x,z) where -- 4
        (r,v) = c' k
        (x,z) = c' v
     f' k =  c (e, c (s' x,y)) where -- 3
        (x,y) = c' k

db :: Cat a => a -> a
db x | e_ x  = e
db x | odd_ x = c (e,x)
db z = c (s x,y) where (x,y) = c' z

hf :: Cat a => a -> a
hf x | e_ x = e
hf z | e_ x = y where (x,y) = c' z
hf z  = c (s' x,y) where (x,y) = c' z

exp2 :: Cat a => a -> a
exp2 x | e_ x = u
exp2 x = c (s' x, u)

log2 :: Cat a => a -> a
log2 x | u_ x = e
log2 x | u_ z = s y where (y,z) = c' x

trailingZeros x | e_ x = e
trailingZeros x | odd_ x = e
trailingZeros x = s (fst (c' x))

