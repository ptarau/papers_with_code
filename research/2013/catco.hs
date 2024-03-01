module CatCo where
-- import Visuals

data Par = L | R deriving (Eq,Show,Read)

type T = [Par]

cons :: (T,T) -> T
cons (xs,L:ys) = L:xs++ys

decons :: T->(T,T)
decons (L:ps) = count_pars 0 ps where
  count_pars 1 (R:ps)  = ([R],L:ps)
  count_pars k (L:ps) = (L:hs,ts) where (hs,ts) = count_pars (k+1) ps
  count_pars k (R:ps) = (R:hs,ts) where (hs,ts) = count_pars (k-1) ps 

to_list :: T -> [T]
to_list [L,R] = []
to_list ps = hs:hss where 
  (hs,ts) = decons ps
  hss = to_list ts

from_list :: [T]->T
from_list [] = [L,R]
from_list (hs:hss) = cons (hs,from_list hss)

oddLen [] = False
oddLen [_] = True
oddLen (_:xs) = not (oddLen xs)

odd_ :: T->Bool
odd_ x = oddLen (to_list x)

even_ :: T->Bool
even_ x =  f (to_list x) where
  f [] =False
  f (y:ys) = oddLen ys

type N = Integer

n :: T->N
n ([L,R]) = 0
n a | even_ a = 2^(n x + 1)*(n xs) where (x,xs) = decons a
n a | odd_ a = 2^(n x + 1)*(n xs+1)-1 where (x,xs) = decons a

t :: N->T
t 0 = [L,R]
t k | k>0 = zs where
  (x,y) = if even k then split0 k else split1 k
  ys = t y
  zs = if x==0 then ys else cons (t (x-1),ys)

split0 :: N->(N,N)
split0 z | z> 0 && even z = (1+x,y) where  
  (x,y) = split0  (z `div` 2)
split0 z = (0,z)

split1 :: N->(N,N)
split1 z | z>0 && odd z = (1+x,y) where  
  (x,y) = split1  ((z-1) `div` 2)
split1 z = (0,z)

e = [L,R]
u = [L,L,R,R]

e_ [L,R] = True
e_ _ = False

u_ [L,L,R,R] = True
u_ _ = False

s x | e_ x = u -- 1
s x | even_ x = from_list (sEven (to_list x)) -- 7
s x | odd_ x = from_list (sOdd (to_list x)) -- 8

sEven (a:x:xs) |e_ a = s x:xs -- 3
sEven (x:xs) = e:s' x:xs -- 4

sOdd [x]= [x,e] -- 2
sOdd (x:a:y:xs) | e_ a = x:s y:xs -- 5
sOdd (x:y:xs) = x:e:(s' y):xs -- 6

s' x | u_ x = e -- 1
s' x | even_ x = from_list (sEven' (to_list x)) -- 8
s' x | odd_ x = from_list (sOdd' (to_list x)) -- 7

sEven' [x,y] |e_ y = [x] -- 2
sEven' (x:b:y:xs) | e_ b = x:s y:xs -- 6
sEven' (x:y:xs) = x:e:s' y:xs -- 5

sOdd' (b:x:xs) | e_ b = s x:xs -- 4
sOdd' (x:xs) = e:s' x:xs -- 3

db x | e_ x = e
db xs | odd_ xs = cons (e,xs)
db xxs | even_ xxs = cons (s x,xs) where (x,xs) = decons xxs

hf x |e_ x = e
hf xxs = if e_ x then xs else cons (s' x,xs) where  (x,xs) = decons xxs

exp2 x | e_ x = u
exp2 x = from_list [s' x,e]

bitsize x = sum (map (n.s) (to_list x))

tsize x =foldr add1 0 (map tsize xs) where
  xs = to_list x
  add1 x y = x + y +1

iterated f a x |e_ a = x
iterated f k x = f (iterated f (s' k) x) 

bestCase k = iterated wterm k e where 
  wterm x = cons (x,e)

worstCase k = iterated (s.db.db) k e 

