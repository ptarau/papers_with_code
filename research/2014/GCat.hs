module GCat where
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

  c' k | k>0 = (max 0 (x-1),ys) where
    b = mod k 2
    (i,j) = dyadicVal (k+b)
    (x,ys) = (i,j-b)

    dyadicVal k | even k = (1+i,j) where  
      (i,j) = dyadicVal (div k 2)
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
     
   g k | c_ w && c_ n && e_ m = 
                         c (x, c (s y,z)) where -- 5
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

leftshiftBy :: Cat a => a -> a -> a
leftshiftBy x y | e_ x = y
leftshiftBy _ y | e_ y = e
leftshiftBy x y | odd_ y = c (s' x, y) 
leftshiftBy x v = c (add x y, z) where (y,z) = c' v

leftshiftBy' :: Cat a => a -> a -> a
leftshiftBy' x k = s' (leftshiftBy x (s k)) 

leftshiftBy'' :: Cat a => a -> a -> a
leftshiftBy'' x k = s' (s' (leftshiftBy x (s (s k))))

add :: Cat a => a -> a -> a
add x y | e_ x = y
add x y | e_ y = x

add x y |even_ x && even_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y
  f EQ = leftshiftBy (s a) (add as bs)
  f GT = leftshiftBy (s b) 
            (add (leftshiftBy (sub a b) as) bs)
  f LT = leftshiftBy (s a) 
           (add as (leftshiftBy (sub b a) bs))

add x y |even_ x && odd_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y
  f EQ = leftshiftBy' (s a) (add as bs)
  f GT = leftshiftBy' (s b)
             (add (leftshiftBy (sub a b) as) bs)
  f LT = leftshiftBy' (s a) 
            (add as (leftshiftBy' (sub b a) bs))

add x y |odd_ x && even_ y = add y x

add x y | odd_ x && odd_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y
  f EQ =  leftshiftBy'' (s a) (add as bs)
  f GT =  leftshiftBy'' (s b) 
             (add (leftshiftBy' (sub a b) as) bs)
  f LT =  leftshiftBy'' (s a) 
            (add as (leftshiftBy' (sub b a) bs))

sub :: Cat a => a -> a -> a
sub x y | e_ y = x
sub x y | even_ x && even_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y
  f EQ = leftshiftBy (s a) (sub as bs)
  f GT = leftshiftBy (s b) 
            (sub (leftshiftBy (sub a b) as) bs)
  f LT = leftshiftBy (s a) 
           (sub as (leftshiftBy (sub b a) bs))

sub x y | odd_ x && odd_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y
  f EQ = leftshiftBy (s a) (sub  as bs)
  f GT = leftshiftBy (s b) 
             (sub (leftshiftBy' (sub a b) as) bs)
  f LT = leftshiftBy (s a) 
           (sub as (leftshiftBy' (sub b a) bs))

sub x y | odd_ x && even_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y
  f EQ = leftshiftBy' (s a) (sub as bs)
  f GT = leftshiftBy' (s b) 
             (sub (leftshiftBy' (sub a b) as) bs)
  f LT = leftshiftBy' (s a) 
           (sub as (leftshiftBy (sub b a) bs)) 

sub x y | even_ x && odd_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y  
  f EQ = s (leftshiftBy (s a) (sub1 as bs))
  f GT = s (leftshiftBy (s b) 
            (sub1 (leftshiftBy (sub a b) as) bs))
  f LT = s (leftshiftBy (s a) 
            (sub1 as (leftshiftBy' (sub b a) bs)))

  sub1 x y = s' (sub x y)  

cmp :: Cat a=> a->a->Ordering
cmp x y | e_ x && e_ y = EQ
cmp x _ | e_ x = LT
cmp _ y | e_ y = GT
cmp x y | u_ x && u_ (s' y) = LT
cmp  x y | u_ y && u_ (s' x) = GT

cmp x y | x' /= y'  = cmp x' y' where
  x' = bitsize x
  y' = bitsize y

cmp xs ys =  
        compBigFirst True True (rev xs) (rev ys) where
  rev = from_list . reverse . to_list

  compBigFirst _ _ x y | e_ x && e_ y = EQ
  compBigFirst False False x y = f (cmp a b) where
    (a,as) = c' x
    (b,bs) = c' y
    f EQ = compBigFirst True True as bs
    f LT = GT
    f GT = LT   
  compBigFirst True True x y = f (cmp a b) where
    (a,as) = c' x
    (b,bs) = c' y
    f EQ = compBigFirst False False as bs
    f LT = LT
    f GT = GT
  compBigFirst False True x y = LT
  compBigFirst True False x y = GT

bitsize :: Cat a => a -> a
bitsize z | e_ z = z
bitsize  z = s (add x (bitsize y)) where (x,y) = c' z

ilog2 :: Cat a => a->a 
ilog2 = s' . bitsize

mul :: Cat a => a -> a -> a
mul x y = f (cmp x y) where
  f GT = mul1 y x
  f _ = mul1 x y

mul1 :: Cat a => a -> a -> a  
mul1 x _ | e_ x = e
mul1 x y | u_ x = y
mul1 a y | even_ a =  
  leftshiftBy (s x) (mul1 z y) where (x,z) = c' a
mul1 a y | odd_ a = 
  sub (leftshiftBy (s x) (mul1 (s z) y)) y where (x,z) = c' a

rightshiftBy :: Cat a => a -> a -> a
rightshiftBy x y | e_ x = y
rightshiftBy _ y | e_ y = e
rightshiftBy x y = f (cmp x a')  where
  (a,b) = c' y
  a' = s a
  f LT = c (sub a x,b) 
  f EQ = b
  f GT = rightshiftBy (sub  x a') b

div_and_rem :: Cat a => a -> a -> (a, a)
div_and_rem x y | LT == cmp x y = (e,x)
div_and_rem x y | c_ y  = (q,r) where 
  (qt,rm) = divstep x y
  (z,r) = div_and_rem rm y
  q = add (exp2 qt) z

  divstep n m = (q, sub n p) where
    q = try_to_double n m e
    p = leftshiftBy q m    

  try_to_double x y k = 
    if (LT==cmp x y) then s' k
    else try_to_double x (db y) (s k)   

divide :: Cat b => b -> b -> b          
divide n m = fst (div_and_rem n m)

remainder :: Cat b => b -> b -> b
remainder n m = snd (div_and_rem n m)

