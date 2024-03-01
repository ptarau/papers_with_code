module FreeAlg where

data AlgU = U | S AlgU deriving (Eq,Read,Show)
data AlgB = B | O AlgB | I AlgB deriving (Eq,Read,Show)
data AlgT = T | C AlgT AlgT deriving (Eq,Read,Show)

sB B = O B            -- 1 --
sB (O x) = I x        -- 2 --
sB (I x) = O (sB x)   -- 3 --
  
sB' (O B) = B         -- 1' --
sB' (O x) = I (sB' x) -- 3' --
sB' (I x) = O x       -- 2' --

u2b ::AlgU -> AlgB
u2b U = B
u2b (S x) = sB (u2b x)  

b2u ::AlgB -> AlgU
b2u B = U
b2u x = S (b2u (sB' x))

binNats = iterate sB B

addB B y = y
addB x B = x
addB(O x) (O y) = I (addB x y)
addB(O x) (I y) = O (sB (addB x y))
addB(I x) (O y) = O (sB (addB x y))
addB(I x) (I y) = I (sB (addB x y))

s T = C T T              -- 1  --
s (C T y) = d (s y)      -- 2  --
s z = C T (d' z)         -- 3  --

s' (C T T) = T           -- 1' --
s' (C T y) = d y         -- 3' --
s' z = C T (s' (d' z))   -- 2' --

d (C a b) = C (s a) b    -- 4  --
d' (C a b) = C (s' a) b  -- 4' --

u2t ::AlgU -> AlgT
u2t U = T
u2t (S x) = s (u2t x)  

t2u ::AlgT -> AlgU
t2u T = U
t2u x = S (t2u (s' x))

treeNats = iterate s T

c',c'' :: AlgT -> AlgT

c' (C x _) = x
c'' (C _ y) = y

c_ :: AlgT -> Bool
c_ (C _ _) = True
c_ T = False

o, o' :: AlgT -> AlgT
o = C T
o' (C T y) = y

o_ :: AlgT -> Bool
o_ (C T _) = True
o_ _ = False

i, i' :: AlgT -> AlgT
i = s . o
i' = o' . s'

i_ :: AlgT -> Bool
i_ (C (C _ _) _) = True
i_ _ = False

b2t :: AlgB -> AlgT
b2t B = T
b2t (O x) = o (b2t x)
b2t (I x) = i (b2t x)

t2b :: AlgT -> AlgB
t2b T = B
t2b x | o_ x = O (t2b (o' x))
t2b x | i_ x = I (t2b (i' x)) 

add T y  = y
add x T  = x
add x y | o_ x && o_ y = i (add (o' x) (o' y))
add x y | o_ x && i_ y = o (s (add (o' x) (i' y)))
add x y | i_ x && o_ y = o (s (add (i' x) (o' y)))
add x y | i_ x && i_ y = i (s (add (i' x) (i' y)))

type N = Integer

n2t :: N -> AlgT
n2t 0 = T
n2t x | x>0 = C (n2t (nC' x)) (n2t (nC'' x)) where
  nC' x|x>0 = 
    if odd x then 0 else 1+(nC'  (x `div` 2))
  nC'' x|x>0 = 
    if odd x then (x-1) `div` 2 else nC'' (x `div` 2)

t2n :: AlgT -> N
t2n T = 0
t2n (C x y) = nC (t2n x) (t2n y) where 
  nC x y = 2^x*(2*y+1)

op1 f x = t2n (f (n2t x))

op2 f x y = t2n (f (n2t x) (n2t y))

check = map (t2n.n2t) [0..31]

sub x T = x
sub y x | o_ y && o_ x = s' (o (sub (o' y) (o' x))) 
sub y x | o_ y && i_ x = s' (s' (o (sub (o' y) (i' x))))
sub y x | i_ y && o_ x = o (sub (i' y) (o' x))  
sub y x | i_ y && i_ x = s' (o (sub (i' y) (i' x)))  

multiply T _ = T
multiply _ T = T  
multiply x y = C (add (c' x) (c' y)) (add a m) where
  (x',y') = (c'' x,c'' y)
  a = add x' y'
  m = s' (o (multiply x' y'))

exp2 x = C x T

to_list :: AlgT -> [AlgT]
to_list T = []
to_list x = (c' x) : (to_list (c'' x))

from_list :: [AlgT] -> AlgT
from_list [] = T
from_list (x:xs) = C x (from_list xs)

list2mset, mset2list :: [AlgT] -> [AlgT] 

list2mset ns = tail (scanl add T ns)
mset2list ms =  zipWith sub ms (T:ms)

to_mset :: AlgT -> [AlgT]      
to_mset = list2mset . to_list

from_mset :: [AlgT] -> AlgT
from_mset = from_list . mset2list

list2set, set2list :: [AlgT] -> [AlgT] 

list2set = (map s') . list2mset . (map s)
set2list = (map s') . mset2list . (map s) 

to_set :: AlgT -> [AlgT]     
to_set = list2set . to_list

from_set :: [AlgT] -> AlgT
from_set = from_list . set2list

