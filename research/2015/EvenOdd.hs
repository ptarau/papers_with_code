module EvenOdd where

data Pos = One |Even Pos [Pos]| Odd Pos [Pos] 
           deriving (Eq, Show, Read)

p' :: Pos -> Integer
p' One = 1
p' (Even x []) = 2^(p' x)
p' (Even x (y:xs)) = 2^(p' x)*(p' (Odd y xs))
p' (Odd x []) = 2^(p' x+1)-1
p' (Odd x (y:xs)) = 2^(p' x)*(p' (Even y xs)+1)-1

to_counters :: Integer  -> (Integer, [Integer])
to_counters k = (b,f b k) where
  parity x = x `mod` 2
  b = parity k

  f _ 1 = []
  f b k | k>1 = x:f (1-b) y where
      (x,y) = split_on b k
  split_on b z | z>1 && parity z == b = (1+x,y) where
    (x,y) = split_on b  ((z-b) `div` 2)
  split_on b z = (0,z)

p :: Integer -> Pos
p k | k>0 = g b ys where
  (b,ks) = to_counters k
  ys = map p ks
  g 1 [] = One
  g 0 (x:xs) = Even x xs
  g 1 (x:xs) = Odd x xs

s :: Pos -> Pos
s One = Even One []
s (Even One []) =  Odd One []
s (Even One (x:xs)) =  Odd (s x) xs
s (Even z xs) = Odd One (s' z : xs)
s (Odd z [])  = Even (s z) []
s (Odd z [One]) = Even z [One]
s (Odd z (One:y:ys)) = Even z (s y:ys)
s (Odd z (x:xs)) = Even z (One:s' x:xs)

s' :: Pos -> Pos
s' (Even One []) = One
s' (Even z []) = Odd (s' z) []
s' (Even z [One]) =  Odd z [One]
s' (Even z (One:x:xs)) =  Odd z (s x:xs)
s' (Even z (x:xs)) =  Odd z (One:s' x:xs)
s' (Odd One []) = Even One []
s' (Odd One (x:xs)) = Even (s x) xs
s' (Odd z xs) = Even One (s' z:xs)

db :: Pos -> Pos
db One = Even One []
db (Even x xs) = Even (s x) xs
db (Odd x xs) = Even One (x:xs)

hf :: Pos -> Pos 
hf (Even One []) = One
hf (Even One (x:xs)) = Odd x xs
hf (Even x xs) = Even px xs where px = s' x

exp2 :: Pos -> Pos
exp2 x = Even x []

log2 :: Pos -> Pos
log2 (Even x []) = x

leftshiftBy :: Pos->Pos->Pos
leftshiftBy k One = Even k [] -- exp2
leftshiftBy k (Even x xs) = Even (add k x) xs
leftshiftBy k (Odd x xs) = Even k (x:xs)

leftshiftBy' :: Pos -> Pos -> Pos
leftshiftBy' x k = s' (leftshiftBy x (s k))

leftshiftBy'' :: Pos -> Pos -> Pos
leftshiftBy'' x k = s' (s' (leftshiftBy x (s (s k))))

rightshiftBy :: Pos -> Pos -> Pos
rightshiftBy k z = f (cmp k x) where
  (b,x,y) = split z
  f LT = fuse (b,sub x k,y)
  f EQ = y
  f GT = rightshiftBy (sub k x) y

split :: Pos -> (Int, Pos, Pos)
split (Even x []) = (0,x,One)
split (Odd x []) = (1,x,One)
split (Even x (y:ys)) = (0,x,Odd y ys)
split (Odd x (y:ys)) = (1,x,Even y ys)

fuse :: (Int, Pos, Pos) -> Pos
fuse (0,x,One) = Even x []
fuse (1,x,One) = Odd x []
fuse (0,x,Odd y ys) = Even x (y:ys)
fuse (1,x,Even y ys) = Odd x (y:ys)

add :: Pos -> Pos -> Pos

add One y = s y
add x One = s x 

add x y = f c where 

  c = cmp a b
  
  (p1,a,as) = split x
  (p2,b,bs) = split y
 
  l 0 0 = leftshiftBy
  l 0 1 = leftshiftBy'
  l 1 0 = leftshiftBy'
  l 1 1 = leftshiftBy''
  
  r _ 0 0 = leftshiftBy
  r GT 0 1 = leftshiftBy
  r LT 1 0 = leftshiftBy
  r _ _ _ = leftshiftBy'
  
  f EQ = l p1 p2 a (add as bs)
  f GT = l p1 p2 b (add (r GT p1 p2 (sub a b) as) bs)
  f LT = l p1 p2 a (add as (r LT p1 p2 (sub b a) bs))  

sub :: Pos -> Pos -> Pos  
sub x One = s' x 
sub x y = f p1 p2 (cmp a b) where 
  
  (p1,a,as) = split x
  (p2,b,bs) = split y
 
  l 0 0 = leftshiftBy
  l 1 1 = leftshiftBy
  
  r 0 0 = leftshiftBy
  r 1 1 = leftshiftBy'
 
  f 1 0 _  = s' (sub (s x) y)
  f 0 1 _  = s' (sub x (s' y))
       
  f _ _ EQ = l p1 p2 a (sub as bs)
  f _ _ GT = l p1 p2 b (sub (r p1 p2 (sub a b) as) bs)
  f _ _ LT = l p1 p2 a (sub as (r p1 p2 (sub b a) bs))  

cmp :: Pos -> Pos -> Ordering
cmp One One = EQ
cmp One _ = LT
cmp _ One = GT
cmp x y | x' /= y'  = cmp x' y' where
  x' = bitsize x
  y' = bitsize y
cmp x y = revCmp x' y' where
  x' = revOrd x
  y' = revOrd y

revCmp :: Pos -> Pos -> Ordering
revCmp One One = EQ
revCmp (Even x xs) (Even y ys) = f (cmp x y) where
    f EQ | xs==[] && ys == [] = EQ
    f EQ = revCmp (Odd x' xs') (Odd y' ys') where
       (x':xs') = xs
       (y':ys') = ys
    f LT = GT
    f GT = LT   
revCmp (Odd x xs) (Odd y ys) = f (cmp x y) where
    f EQ | xs==[] && ys == [] = EQ
    f EQ = revCmp (Even x' xs') (Even y' ys') where
       x':xs' = xs
       y':ys' = ys
    f LT = LT
    f GT = GT 

revCmp (Even _ _) (Odd _ _) = LT
revCmp (Odd _ _) (Even _ _) = GT

revOrd :: Pos -> Pos
revOrd One = One
revOrd (Even x xs) = revPar (Even y ys) where (y:ys) = reverse (x:xs)
revOrd (Odd x xs) = revPar (Odd y ys) where (y:ys) = reverse (x:xs)

revPar :: Pos -> Pos
revPar (Even x xs) | even (length xs)= Even x xs
revPar (Odd x xs) | even (length xs)= Odd x xs
revPar (Even x xs) = Odd x xs
revPar (Odd x xs) = Even x xs

bitsize :: Pos -> Pos
bitsize One = One
bitsize (Even x xs) =  s (foldr add x xs)
bitsize (Odd x xs) =  s (foldr add x xs)

treesize :: Pos -> Pos
treesize One = One
treesize (Even x xs) = foldr add x (map treesize xs)
treesize (Odd x xs) = foldr add x (map treesize xs)

ilog2 :: Pos -> Pos
ilog2 = bitsize . s'

ilog2star :: Pos -> Pos
ilog2star One = One
ilog2star x = s (ilog2star (ilog2 x))

mul :: Pos -> Pos -> Pos
mul x y = f (cmp x y) where
  f GT = mul1 y x
  f _ = mul1 x y

  mul1 One x = x
  mul1 (Even x []) y = leftshiftBy x y
  mul1 (Even x (x':xs)) y =  
     leftshiftBy x (mul1 (Odd x' xs) y)
  mul1 x y  = add y (mul1 (s' x) y)

gcdiv _ One = One
gcdiv One _ = One
gcdiv a b = f px py where
   (px,x,x') = split a 
   (py,y,y') = split b
   
   f 0 0 = g (cmp x y)
   f 0 1 = gcdiv x' b
   f 1 0 = gcdiv a y'
   f 1 1 = h (cmp a b)
   
   g LT = fuse (0,x,gcdiv x' (fuse (0,sub y x,y'))) 
   g EQ = fuse (0,x,gcdiv x' y')
   g GT = fuse (0,y,gcdiv y' (fuse (0,sub x y,x'))) 
   
   h LT = gcdiv a (sub b a)
   h EQ = a
   h GT = gcdiv b (sub a b)  

data Z = Zero | Plus Pos | Minus Pos 
  deriving (Eq, Show, Read)

z' :: Z -> Integer
z' Zero = 0
z' (Plus x) = p' x
z' (Minus x) = - (p' x)

z :: Integer -> Z
z 0 = Zero
z k | k>0 = Plus (p k)
z k | k<0 = Minus (p (-k))

opposite Zero = Zero
opposite (Plus x) = Minus x
opposite (Minus x) = Plus x

sZ :: Z -> Z
sZ Zero = Plus One
sZ (Plus x) = Plus y where  y = s x
sZ (Minus One) = Zero
sZ (Minus x) = Minus y where y = s' x

sZ' :: Z -> Z
sZ' Zero = Minus One
sZ' (Minus x) = Minus y where y = s x
sZ' (Plus One) = Zero
sZ' (Plus x) = Plus y where y = s' x

cons :: (Pos,Pos)->Pos
cons (One,One) = Even One []
cons (Even x xs,One)  =  Odd (hf (Even x xs)  ) []
cons (Odd x xs,One)  = Even (hf (s (Odd x xs)   )) []
cons (x,Even y ys) = Odd x (y:ys)
cons (x,Odd y ys) = Even x (y:ys)

decons :: Pos->(Pos,Pos)
decons (Even x []) = (s' (db x),One)
decons (Even x (y:ys)) = (x,Odd y ys)
decons (Odd x []) = (db x,One)
decons (Odd x (y:ys)) = (x,Even y ys)

to_list :: Pos -> [Pos]
to_list One = []
to_list z = x : to_list y where (x,y) = decons z

from_list :: [Pos] -> Pos
from_list [] = One
from_list (x:xs) = cons (x,from_list xs)

list2set, set2list :: [Pos] -> [Pos]

list2set [] = []
list2set (n:ns) = scanl add n ns

set2list [] = []
set2list (m:ms) = m : zipWith sub ms (m:ms)

to_set :: Pos -> [Pos]  
to_set = list2set . to_list

from_set :: [Pos] -> Pos
from_set = from_list . set2list

