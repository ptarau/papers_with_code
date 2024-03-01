module Arith where

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
s (Even z xs) = Odd One (pz : xs) where pz = s' z
s (Odd z [])  = Even (s z) []
s (Odd z [One]) = Even z [One]
s (Odd z (One:y:ys)) = Even z (s y:ys)
s (Odd z (x:xs)) = Even z (One:px:xs) where px = s' x

s' :: Pos -> Pos
s' (Even One []) = One
s' (Even z []) = Odd pz [] where pz = s' z
s' (Even z [One]) =  Odd z [One]
s' (Even z (One:x:xs)) =  Odd z (s x:xs)
s' (Even z (x:xs)) =  Odd z (One:px:xs) where px = s' x
s' (Odd One []) = Even One []
s' (Odd One (x:xs)) = Even (s x) xs
s' (Odd z xs) = Even One (pz:xs) where pz = s' z

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
cons ((Even x xs),One)  =  Odd (hf (Even x xs)  ) []
cons ((Odd x xs),One)  = Even (hf (s (Odd x xs)   )) []
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

data Term a = Var a | Const a | Fun a [Term a] 
  deriving (Eq,Show,Read)

toTerm :: Pos -> Term Pos
toTerm One = Var One
toTerm (Odd x []) = Var (s x)
toTerm (Even x []) = Const x
toTerm (Odd x (y:xs)) = Fun (s' (db x))
  (map toTerm (y:xs))
toTerm (Even x (y:xs)) = Fun (db x) (map toTerm (y:xs))

fromTerm :: Term Pos -> Pos
fromTerm (Var One) = One
fromTerm (Var y) = Odd (s' y) []
fromTerm (Const x) = Even x []
fromTerm (Fun One xs) = Odd One (map fromTerm xs)
fromTerm (Fun x@(Odd _ _) xs) = Odd (hf (s x)) (map fromTerm xs)
fromTerm (Fun x@(Even _ _) xs) = Even (hf x) (map fromTerm xs)

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

square :: Pos -> Pos
square One = One
square z = f b y where
  (b,x,y) = split z
  f 0 y = fuse (0,db x,square y)
  f 1 One = sub (exp2 (db (s x))) (exp2' (s x))
  f 1 y = r where
     k = add (square y) (db y)
     m = fuse (1,db x,k)
     r = sub m (db z)

exp2' :: Pos -> Pos
exp2' x = Odd x []

superSquare One a = square a
superSquare x a = square (superSquare (s' x) a)

pow a One = a
pow a (Even x []) = superSquare x a
pow a (Even x (x':xs)) = 
  pow (superSquare x a) (Odd x' xs)
pow a x  = mul a (pow a (s' x))

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

addZ :: Z -> Z -> Z
addZ Zero x = x
addZ x Zero = x
addZ (Plus x) (Plus y) = Plus (add x y)
addZ (Minus x) (Minus y) = Minus (add x y)
addZ (Plus x) (Minus y) = f (cmp x y) where
  f EQ = Zero
  f LT = Minus (sub y x)
  f GT = Plus (sub x y)
addZ (Minus y) (Plus x) = f (cmp x y) where
  f EQ = Zero
  f LT = Minus (sub y x)
  f GT = Plus (sub x y)

subZ :: Z -> Z -> Z
subZ x y = addZ x (opposite y)

cmpZ :: Z -> Z -> Ordering
cmpZ Zero Zero = EQ
cmpZ Zero (Plus _) = LT 
cmpZ Zero (Minus _) = GT
cmpZ (Minus _) Zero = LT
cmpZ (Plus _) Zero = GT 
cmpZ (Minus x) (Minus y) = cmp y x
cmpZ (Plus x) (Plus y) = cmp x y
cmpZ (Minus _) (Plus _) = LT
cmpZ (Plus _) (Minus _) = GT

shiftBy :: Z -> Z -> Z
shiftBy Zero x = x
shiftBy (Plus x) (Plus y) = Plus (leftshiftBy x y) 
shiftBy (Minus x) (Plus y) = Plus (rightshiftBy x y)
shiftBy (Plus x) (Minus y) = Minus (leftshiftBy x y) 
shiftBy (Minus x) (Minus y) = Minus (rightshiftBy x y) 

mulZ Zero _ = Zero
mulZ _ Zero = Zero
mulZ (Plus x) (Plus y) = Plus (mul x y)
mulZ (Plus x) (Minus y) = Minus (mul x y)
mulZ (Minus x) (Plus y) = Minus (mul x y)
mulZ (Minus x) (Minus y) = Plus (mul x y)

divWithPos :: Z -> Pos -> (Z, Z) 
divWithPos n One = (n,Zero)  
divWithPos n k = divStep aligned Zero n where 
    d = Plus k  
    
    up Zero = Zero
    up (Plus x) = Plus (db x)
    
    down Zero = Zero
    down (Plus x@(Even _ _)) = Plus (hf x)
    down (Plus x@(Odd _ _)) = Plus (hf (s' x))
    
    aligned = down (until over up d)
     
    over x = cmpZ x n == GT
    
    divStep t q r | cmpZ t d == LT    = (q, r)
    divStep t q r | cmpZ t r /= GT  = 
       divStep (down t) (sZ (up q )) (subZ r t)
    divStep t q r = divStep (down t) (up q)     r

div_and_rem :: Z -> Z -> (Z, Z)  
div_and_rem Zero x | x/=Zero = (Zero,Zero)
div_and_rem (Plus x) (Plus y) = divWithPos (Plus x) y
div_and_rem (Minus x) (Minus y) = (a,opposite b) where 
  (a,b)=divWithPos (Plus x) y
div_and_rem (Plus x) (Minus y) = f (divWithPos (Plus x) y) where
  f (q,Zero)= (opposite q,Zero)
  f (q,Plus r) = (opposite q, Plus r)
div_and_rem (Minus x) (Plus y) = f (divWithPos (Plus x) y) where
  f (q,Zero)= (opposite q,Zero)
  f (q,Plus r) = (opposite q,Minus r)  
  
divide n m = fst (div_and_rem n m)

remainder n m = snd (div_and_rem n m)

