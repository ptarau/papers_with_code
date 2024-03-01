module HBS where
import HBin
--import Visuals

cons :: (T,T)->T
cons (E,y) = o y
cons (x,y) = s (f (s' (o y))) where
  f E = V (s' x) []
  f (W y xs) = V (s' x) (y:xs)

decons :: T -> (T,T)
decons z | o_ z = (E, o' z)
decons z | i_ z = (s x, g xs) where  
  V x xs = s' z
  
  g [] = E
  g (y:ys) = s (i' (W y ys)) 

to_list :: T -> [T]
to_list z | e_ z = []
to_list z = x : to_list y where (x,y) = decons z

from_list :: [T] -> T
from_list [] = E
from_list (x:xs) = cons (x,from_list xs)

list2mset, mset2list :: [T] -> [T]

list2mset [] = []
list2mset (n:ns) = scanl add n ns

mset2list [] = []
mset2list (m:ms) = m : zipWith sub ms (m:ms)

list2set, set2list :: [T] -> [T]

list2set = (map s') . list2mset . (map s)

set2list = (map s') . mset2list . (map s) 

to_mset :: T -> [T]
to_mset = list2mset . to_list

from_mset :: [T] -> T
from_mset = from_list . mset2list

to_set :: T -> [T]  
to_set = list2set . to_list

from_set :: [T] -> T
from_set = from_list . set2list

data Iso a b = Iso (a->b) (b->a)

from (Iso f _) = f
to (Iso _ f') = f'

as :: Iso a b -> Iso c b -> c -> a
as that this x = to that (from this x)

nat = Iso id id

list, mset, set :: Iso [T] T

list = Iso from_list to_list

mset = Iso from_mset to_mset

set = Iso from_set to_set

borrow1 :: Iso b c -> (b -> b) -> Iso a c -> a -> a
borrow1 lender f borrower = 
  as borrower lender . f . as lender borrower

borrow2 :: Iso c b -> (c->c->c) -> Iso a b -> (a->a->a)
borrow2 lender op borrower x y =  
  as borrower lender (op x' y') where
    x'= as lender borrower x
    y'= as lender borrower y

type N = Integer
bitnat :: Iso N T
bitnat = Iso t n

decons' :: T->(T,T)
decons' (V x []) = (s' (o x),E)
decons' (V x (y:ys)) = (x,W y ys)
decons' (W x []) = (o x,E)
decons' (W x (y:ys)) = (x,V y ys)

cons' :: (T,T)->T
cons' (E,E) = V E []
cons' (x,E) | o_ x =  W (o' x) []
cons' (x,E) | i_ x = V (o' (s x)) []
cons' (x,V y ys) = W x (y:ys)
cons' (x,W y ys) = V x (y:ys)

to_list' :: T -> [T]
to_list' x | e_ x = []
to_list' x = hd : (to_list' tl) where (hd,tl)=decons' x

from_list' :: [T] -> T
from_list' [] = E
from_list' (x:xs) = cons' (x,from_list' xs)

to_mset' = list2mset . to_list'
from_mset' = from_list' . mset2list

to_set' = list2set . to_list'
from_set' = from_list' . set2list

list', mset', set' :: Iso [T] T

list' = Iso from_list' to_list'

mset' = Iso from_mset' to_mset'

set' = Iso from_set' to_set'

data H = H [H] deriving (Eq,Read,Show) 

t2h :: (T -> [T]) -> T -> H
t2h f E = H []
t2h f n = H (map (t2h f) (f n))

h2t :: ([T] -> T) -> H -> T
h2t g (H []) = E
h2t g (H hs) = g (map (h2t g) hs)

hfl, hfm, hfs :: Iso H T
hfl = Iso  (h2t from_list) (t2h to_list)
hfm = Iso  (h2t from_mset) (t2h to_mset)
hfs = Iso (h2t from_set) (t2h to_set)

ackermann :: H -> T
ackermann (H xs) = foldr add E (map (exp2 . ackermann) xs)

hfl', hfm', hfs' :: Iso H T
hfl' = Iso  (h2t from_list') (t2h to_list')
hfm' = Iso  (h2t from_mset') (t2h to_mset')
hfs' = Iso (h2t from_set') (t2h to_set')

hdual :: H -> H
hdual (H []) = H []
hdual (H (x:xs)) = H (hdual (H xs): ys) where
  H ys = hdual x

tdual :: T -> T
tdual = borrow1 hfl' hdual nat

data Term a = Var a | Const a | Fun a [Term a] 
  deriving (Eq,Show,Read)

toTerm :: T -> Term N
toTerm E = Var 0
toTerm (V x []) = Var (n x+1)
toTerm (W x []) = Const (n x)
toTerm (V x xs) = Fun (2*n x+1) (map toTerm xs)
toTerm (W x xs) = Fun (2*n x) (map toTerm xs)

fromTerm :: Term N -> T
fromTerm (Var 0) = E
fromTerm (Var y) = V (s' (t y)) []
fromTerm (Const x) = W (t x) []
fromTerm (Fun k xs) | odd k = 
  V (o' (t k)) (map fromTerm xs)
fromTerm (Fun k xs) | even k = 
  W (hf (t k)) (map fromTerm xs)

bitwiseOr :: T -> T -> T
bitwiseOr E y = y
bitwiseOr x E = x
bitwiseOr x y = s (bwOr (s' x) (s' y))

bwOr :: T -> T -> T
bwOr E y | o_ y  = s y
bwOr x E | o_ x  = s x
bwOr E y = y
bwOr x E = x

bwOr x y | o_ x && o_ y = f (cmp a b) where
  (a,as) = osplit x
  (b,bs) = osplit y
  f EQ = orApplyO (s a) as bs
  f GT = orApplyO (s b) (otimes (sub a b) as) bs
  f LT = orApplyO (s a) as (otimes (sub b a) bs)

bwOr x y |o_ x && i_ y = f (cmp a b) where
  (a,as) = osplit x
  (b,bs) = isplit y
  f EQ = orApplyI (s a) as bs
  f GT = orApplyI (s b) (otimes (sub a b) as) bs
  f LT = orApplyI (s a) as (itimes (sub b a) bs)  

bwOr x y |i_ x && o_ y = f (cmp a b) where
  (a,as) = isplit x
  (b,bs) = osplit y
  f EQ = orApplyI (s a) as bs
  f GT = orApplyI (s b) (itimes (sub a b) as) bs
  f LT = orApplyI (s a) as (otimes (sub b a) bs)  

bwOr x y |i_ x && i_ y = f (cmp a b) where
  (a,as) = isplit x
  (b,bs) = isplit y
  f EQ = orApplyI (s a) as bs
  f GT = orApplyI (s b) (itimes (sub a b) as) bs
  f LT = orApplyI (s a) as (itimes (sub b a) bs)  

orApplyO k x y =  otimes k (bwOr x y) 

orApplyI k x y =  itimes k (bwOr x y) 

bitwiseNot :: T -> T -> T
bitwiseNot k x = sub y x where y = s' (exp2 k)

bitwiseAndNot :: T -> T -> T  
bitwiseAndNot x y = bitwiseNot l d  where
  l = max2 (bitsOf x) (bitsOf y)
  d = bitwiseOr (bitwiseNot l x) y

max2 :: T -> T -> T
max2 x y = if LT==cmp x y then y else x

bitsOf :: T -> T
bitsOf E = s E
bitsOf x = s (ilog2 x)

bitwiseAnd :: T -> T -> T
bitwiseAnd x y = bitwiseNot l d where
  l = max2 (bitsOf x) (bitsOf y)
  d = bitwiseOr (bitwiseNot l x) (bitwiseNot l y)


bitwiseXor :: T -> T -> T
bitwiseXor x y = 
  bitwiseOr (bitwiseAndNot x y) (bitwiseAndNot y x)

setIntersection :: [T]->[T]->[T]
setIntersection = borrow2 nat bitwiseAnd set

setUnion :: [T]->[T]->[T]
setUnion = borrow2 nat bitwiseOr set

var :: T -> T -> T
var n k = repeatBlocks nbBlocks blockSize mask where 
  k' = s k
  nbBlocks = exp2 k'
  blockSize = exp2 (sub n k')
  mask = s' (exp2 blockSize) 

  repeatBlocks E _ _ = E
  repeatBlocks k l mask = 
   if o_ k then r else add mask r where
    r = leftshiftBy l (repeatBlocks (s' k) l mask)

cnf = andN (map orN cls) where
  cls = [[v0',v1',v2],[v0,v1',v2],
         [v0',v1,v2'],[v0',v1',v2'],[v0,v1,v2]]
  
  v0 = var (t 3) (t 0)
  v1 = var (t 3) (t 1)
  v2 = var (t 3) (t 2)

  v0' = bitwiseNot (exp2 (t 3)) v0
  v1' = bitwiseNot (exp2 (t 3)) v1
  v2' = bitwiseNot (exp2 (t 3)) v2

  orN (x:xs) = foldr bitwiseOr x xs
  andN (x:xs) = foldr bitwiseAnd x xs

bitval :: T -> T -> T -> N
bitval numberOfVars k x | cmp k numberOfRows == LT && 
                cmp x (s truthTableStart) == LT = 
  nthBit k (add truthTableStart x) where
    numberOfRows = exp2 numberOfVars
    truthTableStart = s' (exp2 numberOfRows)

nthBit k (V x (y:xs)) | cmp k x == GT = 
  nthBit (sub k (s x)) (W y xs) 
nthBit k (V _ _) = 0 
nthBit k (W x (y:xs)) | cmp k x == GT = 
  nthBit (sub k (s x)) (V y xs) 
nthBit k (W _ _) = 1

rev :: T -> T
rev E = E
rev (V x xs) = r where
  y:ys = reverse (x:xs)
  r = if o_ (len (x:xs)) then V y ys else W y ys
rev (W x xs) = r where
  y:ys = reverse (x:xs)
  r = if o_ (len (x:xs)) then W y ys else V y ys

as_bin E = V E []
as_bin x = (rev . i . rev . s') x

as_bbin (V E []) = E
as_bbin x = (s . rev . i' . rev) x

neg = dual

conj :: T -> T -> T
conj E _ = E
conj _ E = E
conj x y | o_ x && o_ y = o (conj (o' x) (o' y))
conj x y | o_ x && i_ y = o (conj (o' x) (i' y))
conj x y | i_ x && o_ y = o (conj (i' x) (o' y))
conj x y | i_ x && i_ y = i (conj (i' x) (i' y))

xdisj :: T -> T -> T
xdisj E _  = E
xdisj _ E  = E
xdisj x y | o_ x && o_ y = o (xdisj (o' x) (o' y))
xdisj x y | o_ x && i_ y = i (xdisj (o' x) (i' y))
xdisj x y | i_ x && o_ y = i (xdisj (i' x) (o' y))
xdisj x y | i_ x && i_ y = o (xdisj (i' x) (i' y))

disj :: T -> T -> T
disj x y = neg (conj (neg x) (neg y))

geq, eq :: T -> T -> T
geq x y = neg (conj (neg x) y) 

eq x y = conj (geq x y) (geq y x)

inf1 E = E
inf1 (V x []) = V x []
inf1 (V x [y]) = V (s (add x y)) []
inf1 (V x (y:z:xs)) = V (s (s (add (add x y) z))) xs
inf1 (W x []) = V x []
inf1 (W x (y:xs)) = V (s (add x y)) xs

sup1 E = E
sup1 (V x []) = W x []
sup1 (V x (y:xs)) = W (s (add x y)) xs
sup1 (W x []) = W x []
sup1 (W x [y]) = W (s (add x y)) []
sup1 (W x (y:z:xs)) = W (s (s (add (add x y) z))) xs

fixpoint f x = r where
  p (a,b) = a/=b
  xs = iterate f x
  zs = zip xs (tail xs)
  ps = takeWhile p zs
  qs= snd (unzip ps)
  r = if []==qs then x else (last qs)

l E = "0"
l (V x []) = "2^{"++"{"++(l x)++"}+1}-1"
l (W x []) = "2^{"++"{"++(l x)++"}+2}-2"  --  2^(l x+2)-2
l (V x (y:xs)) = "({"++(l u)++"}+1)"++"2^{"++"{"++(l x)++"} + 1}-1" where u = W y xs
l (W x (y:xs)) = "({"++(l u)++"}+2)"++"2^{"++"{"++(l x)++"} + 1}-2" where u = V y xs

