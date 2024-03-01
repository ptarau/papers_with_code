module SYNASC_freealg where

data AlgU = U | S AlgU deriving (Eq,Read,Show)
data AlgB = B | O AlgB | I AlgB deriving (Eq,Read,Show)
data AlgT = T | C AlgT AlgT deriving (Eq,Read,Show)

-- successor
sB B = O B            -- 1 --
sB (O x) = I x        -- 2 --
sB (I x) = O (sB x)   -- 3 --

-- predecessor  
sB' (O B) = B         -- 1' --
sB' (O x) = I (sB' x) -- 3' --
sB' (I x) = O x       -- 2' --

u2b :: AlgU -> AlgB
u2b U = B
u2b (S x) = sB (u2b x)  

b2u :: AlgB -> AlgU
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

u2t :: AlgU -> AlgT
u2t U = T
u2t (S x) = s (u2t x)  

t2u :: AlgT -> AlgU
t2u T = U
t2u x = S (t2u (s' x))

treeNats = iterate s T

type N = Integer

n2t :: N -> AlgT
n2t 0 = T
n2t x | x>0 = C (n2t (nC' x)) (n2t (nC'' x)) where
  nC' x|x>0 = if odd x then 0 else 1+(nC'  (x `div` 2))
  nC'' x|x>0 = 
    if odd x then (x-1) `div` 2 else nC'' (x `div` 2)

t2n :: AlgT -> N
t2n T = 0
t2n (C x y) = nC (t2n x) (t2n y) where 
  nC x y = 2^x*(2*y+1)

c',c'' :: AlgT -> AlgT

c' (C x _) = x
c'' (C _ y) = y

c_ :: AlgT -> Bool
c_ (C _ _) = True
c_ T = False

o, o', i, i' :: AlgT -> AlgT
o_, i_ :: AlgT -> Bool

o = C T
o' (C T y) = y
o_ (C x _) = x == T

i = s . o
i' = o' . s'
i_ (C x _) = x /= T

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

sub x T = x
sub y x | o_ y && o_ x = s' (o (sub (o' y) (o' x))) 
sub y x | o_ y && i_ x = s' (s' (o (sub (o' y) (i' x))))
sub y x | i_ y && o_ x = o (sub (i' y) (o' x))  
sub y x | i_ y && i_ x = s' (o (sub (i' y) (i' x)))  

cmp T T  = EQ
cmp T _ = LT
cmp _ T = GT
cmp x y | o_ x && o_ y = cmp (o' x) (o' y)
cmp x y | i_ x && i_ y = cmp (i' x) (i' y)
cmp x y | o_ x && i_ y = strengthen (cmp (o' x) (i' y)) LT
cmp x y | i_ x && o_ y = strengthen (cmp (i' x) (o' y)) GT

strengthen EQ stronger = stronger
strengthen rel _ = rel

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

data HFS = H [HFS] deriving (Eq,Read,Show)

hfs2nat t = rank set2nat t
rank g (H ts) = g (map (rank g) ts)
set2nat ns = sum (map (2^) ns)

nat2hfs n = unrank nat2set n
unrank f n = H (map (unrank f) (f n))
nat2set n = nat2exps n 0 where
  nat2exps 0 _ = []
  nat2exps n x = 
    if (even n) then xs else (x:xs) where
      xs=nat2exps (n `div` 2) (succ x)

sH (H xs) = H (lift (H []) xs)
 
sH' (H (x:xs)) = H (lower x xs)
     
lift k (x:xs) | k == x = lift (sH k) xs
lift k xs = k:xs

lower (H []) xs = xs
lower k xs = lower l (l:xs) where l = sH' k

-- "empty" and its recognizer
eH = H []
eH_ x = x == H []

-- constructors
oH (H xs) = sH (H (map sH xs))
iH = sH . oH

-- destructors
oH' x | oH_ x = H (map sH' ys) where H ys = sH' x
iH' x = oH' (sH' x) 

-- recognizers
oH_ (H (x:_)) = eH_ x
iH_ x = not (eH_ x || oH_ x) 

data Par = L | R deriving (Eq,Show,Read)

-- deconstructs a list of balanced parentheses into (head,tail)
decons (L:ps) = (reverse hs, ts) where
  (hs,ts) = count_pars 0 ps [] 
  count_pars 1 (R:ps) hs = (R:hs,L:ps)
  count_pars k (L:ps) hs = count_pars (k+1) ps (L:hs)
  count_pars k (R:ps) hs = count_pars (k-1) ps (R:hs)  

-- constructs a list of balanced parentheses from (head,tail)
cons (xs, L:ys) = L:xs ++ ys

-- constructor + recognizer for empty
eP = [L,R]
eP_ x = (x == eP)

-- successor
sP z | eP_ z = cons (eP,eP)                         -- 1  --
sP z | eP_ x = dP (sP y) where (x,y) = decons z     -- 2  --
sP z = cons (eP, dP' z)                             -- 3  --

-- predecessor
sP' z | eP_ x && eP_ y = eP where (x,y) = decons z  -- 1' --
sP' z | eP_ x = dP y where (x,y) = decons z         -- 3' --
sP' z = cons (eP, sP' (dP' z))                      -- 2' --

-- double
dP z = cons (sP a,b) where (a,b) = decons z         -- 4  --

-- half of non-zero even
dP' z = cons (sP' a,b) where (a,b) = decons z       -- 4' --

n2q 0 = (1,1)
n2q x | odd x =  (f0,f0+f1) where 
  (f0,f1) = n2q (div (x-1) 2) 
n2q x | even x  = (f0+f1,f1) where 
  (f0,f1) = n2q ((div x 2)-1)

q2n (1,1) = 0
q2n (a,b) = f ordrel where 
  ordrel = compare a b 
  f GT = 2*(q2n (a-b,b))+2
  f LT = 2*(q2n (a,b-a))+1

t2q T = (o T,o T)
t2q n | o_ n = (f0,add f0 f1) where (f0,f1)=t2q (o' n)
t2q n | i_ n = (add f0 f1,f1) where (f0,f1)=t2q (i' n)

q2t q | q == (o T,o T) = T
q2t (a,b) = f ordrel where 
  ordrel = cmp a b 
  f GT = i (q2t (sub a b,b))
  f LT = o (q2t (a,sub b a))

data M = M|V M M |W M M deriving (Show, Read, Eq)

eM = M
eM_ x = x == eM

sM x | eM_ x = oM x
sM x | oM_ x = iM (oM' x)
sM x | iM_ x = oM (sM (iM' x))
  
sM' x | x == oM eM = eM
sM' x | oM_ x = iM (sM' (oM' x))
sM' x | iM_ x = oM (iM' x)  

oM (V x y) = V (sM x) y
oM w = V M w

iM (W x y) = W (sM x) y
iM v = W M v
  
oM' (V M y) = y
oM' (V x y) = V (sM' x) y

iM' (W M y) = y
iM' (W x y) = W (sM' x) y
  
oM_ (V _ _ ) = True
oM_ _ = False

iM_ (W _ _ ) = True
iM_ _ = False

