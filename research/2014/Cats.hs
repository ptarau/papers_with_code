module Cats where
-- import Visuals

data T = E | C T T deriving (Eq,Show,Read)

data M = F [M] deriving (Eq,Show,Read)

data Par = L | R deriving (Eq,Show,Read)

data P = P [Par] deriving (Eq,Show,Read)

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

instance Cat P where
 e = P [L,R]
 
 c (P xs,P (L:ys)) = P (L:xs++ys)
 
 c' (P (L:ps)) = (P xs,P ys) where
  (xs,ys) = count_pars 0 ps
  
  count_pars 1 (R:ps)  = ([R],L:ps)
  count_pars k (L:ps) = (L:hs,ts) where 
     (hs,ts) = count_pars (k+1) ps
  count_pars k (R:ps) = (R:hs,ts) where 
     (hs,ts) = count_pars (k-1) ps 

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

p :: Cat a => a->P
p = view

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
     g' k | c_ v && c_ w && e_ r = c (x, c (s y,z)) where -- 6
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
  f GT = leftshiftBy (s b) (add (leftshiftBy (sub a b) as) bs)
  f LT = leftshiftBy (s a) (add as (leftshiftBy (sub b a) bs))

add x y |even_ x && odd_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y
  f EQ = leftshiftBy' (s a) (add as bs)
  f GT = leftshiftBy' (s b) (add (leftshiftBy (sub a b) as) bs)
  f LT = leftshiftBy' (s a) (add as (leftshiftBy' (sub b a) bs))

add x y |odd_ x && even_ y = add y x

add x y | odd_ x && odd_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y
  f EQ =  leftshiftBy'' (s a) (add as bs)
  f GT =  leftshiftBy'' (s b) (add (leftshiftBy' (sub a b) as) bs)
  f LT =  leftshiftBy'' (s a) (add as (leftshiftBy' (sub b a) bs))

sub :: Cat a => a -> a -> a
sub x y | e_ y = x
sub x y | even_ x && even_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y
  f EQ = leftshiftBy (s a) (sub as bs)
  f GT = leftshiftBy (s b) (sub (leftshiftBy (sub a b) as) bs)
  f LT = leftshiftBy (s a) (sub as (leftshiftBy (sub b a) bs))

sub x y | odd_ x && odd_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y
  f EQ = leftshiftBy (s a) (sub  as bs)
  f GT = leftshiftBy (s b) (sub (leftshiftBy' (sub a b) as) bs)
  f LT = leftshiftBy (s a) (sub as (leftshiftBy' (sub b a) bs))

sub x y | odd_ x && even_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y
  f EQ = leftshiftBy' (s a) (sub as bs)
  f GT = leftshiftBy' (s b) (sub (leftshiftBy' (sub a b) as) bs)
  f LT = leftshiftBy' (s a) (sub as (leftshiftBy (sub b a) bs)) 

sub x y | even_ x && odd_ y = f (cmp a b) where
  (a,as) = c' x
  (b,bs) = c' y  
  f EQ = s (leftshiftBy (s a) (sub1 as bs))
  f GT = s (leftshiftBy (s b) (sub1 (leftshiftBy (sub a b) as) bs))
  f LT = s (leftshiftBy (s a) (sub1 as (leftshiftBy' (sub b a) bs)))

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

cmp xs ys = compBigFirst True True (rev xs) (rev ys) where
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
mul1 a y | even_ a =  leftshiftBy (s x) (mul1 xs y) where (x,xs) = c' a
mul1 a y | odd_ a = (sub (leftshiftBy (s x) (mul1 (s xs) y)) y) where
  (x,xs) = c' a

square :: Cat a => a -> a
square x = mul1 x x

pow :: Cat a => a -> a -> a
pow _ b | e_ b = u
pow a _ | e_ a = e
pow a b | even_ a = c (s' (mul (s x) b),ys) where 
  (x,xs) = c' a
  ys = pow xs b
pow a b | even_ b = pow (superSquare y a) ys where
  (y,ys) = c' b
  superSquare k x | e_ k = square x
  superSquare k x = square (superSquare (s' k) x)
pow x y = mul x (pow x (s' y)) 

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

catsize :: Cat a => a -> a
catsize z | e_ z = z
catsize  z = s (add (catsize x) (catsize y)) where (x,y) = c' z

cat :: N->N
cat 0 = 1
cat n | n>0 = (2*(2*n-1)*(cat (n-1))) `div` (n+1)

catsized :: Cat a => a -> [a]
catsized a = take k [x | x<-iterate s e,catsize x == a] where
  k = fromIntegral (cat (n a))

iterated :: Cat a => (t -> t) -> a -> t -> t 
iterated f k x |e_ k = x
iterated f k x = f (iterated f (s' k) x) 

bestCase :: Cat a => a -> a
bestCase k = iterated f k e where f x = c (x,e)

worstCase :: Cat a => a -> a
worstCase k = iterated f k e where f x = c (e,x)

dual :: Cat a => a -> a
dual x | e_ x = e
dual z = c (dual y,dual x) where (x,y) = c' z

min2, max2 :: Cat a => a -> a -> a
min2 x y = if LT==cmp x y then x else y
max2 x y = if LT==cmp x y then y else x

maxTdepth :: Cat a => a -> a
maxTdepth z | e_ z = z
maxTdepth z = s (max2  (maxTdepth x) (maxTdepth y)) where (x,y) = c' z

minTdepth :: Cat a => a -> a
minTdepth z | e_ z = z
minTdepth z = s (min2  (minTdepth x) (minTdepth y)) where (x,y) = c' z  

maxMdepth :: Cat a => a -> a
maxMdepth z | e_ z = z
maxMdepth z = s (foldr max2 m ms) where
  (m:ms) = map maxMdepth (to_list z)

minMdepth :: Cat a => a -> a
minMdepth z | e_ z = z
minMdepth z = s (foldr min2 m ms) where
  (m:ms) = map minMdepth (to_list z)

-- equivalent to maxMdepth

maxMdepth' :: Cat a => a -> a
maxMdepth' z | e_ z = z
maxMdepth' z = s (max2 (maxMdepth' x) y') where 
  (x,y) = c' z
  y' = if c_ y then maxMdepth' (snd (c' y)) else e


rratio x = fromIntegral md / fromIntegral td where
  md = maxMdepth x
  td = maxTdepth x 
  
rdif x = fromIntegral td - fromIntegral md where
  md = maxMdepth x
  td = maxTdepth x   

mersennePrime f = s' (exp2 (f 57885161))
generizedFermatPrime f = s (leftshiftBy (f 9167433) (f 27653))
cullenPrime f = s (leftshiftBy x x) where x = f 6679881
woodallPrime f = s' (leftshiftBy x x) where x = f 3752948
prothPrime f = s (leftshiftBy (f 13018586) (f 19249))
sophieGermainPrime f = s' (leftshiftBy (f 666667) (f 18543637900515))
twinPrimes f = (s' y,s y) where 
  y = leftshiftBy (f 666669) (f 3756801695685)


giants :: Cat a => (N -> a) -> ([String], [a])
giants f = (ns,ps) where
  ps = [mersennePrime f, generizedFermatPrime f,  cullenPrime f, woodallPrime f,
        sophieGermainPrime f, fst (twinPrimes f), snd (twinPrimes f)]
  ns = ["mersenne48", "generizedFermatPrime",  "cullenPrime", "woodallPrime",
        "sophieGermainPrime", "twinPrimes1", "twinPrimes2"]
        
-- sizes for primes and their  duals      
sizes d f =  zip (zip3 ns bs cs) (zip3 maxs tmaxs dmaxs) where 
  ps = map d (snd (giants f))
  ns = fst (giants f)
  
  bs = map (n.catsize) ps
  cs = map (n.catsize) ps
  maxs = map (n.maxMdepth) ps
  tmaxs = map (n.maxTdepth) ps
  dmaxs = map (n.maxMdepth.dual) ps

-- usage: showSizes t
showSizes f = mapM_ print (sizes id f)
showDSizes f = mapM_ print (sizes dual f)

-- usage: compDuals t
compDuals f = zip ns (zipWith cmp ps ds) where
  ps = snd (giants f)
  ds = map dual ps
  ns = fst (giants f)

ilog2star :: Cat a => a->a
ilog2star x | e_ x = x
ilog2star x = s (ilog2star (ilog2 x))


logsizes =  map (n.ilog2star) (snd (giants t))

dlogsizes = map (n.ilog2star) (map dual (snd (giants t)))

maxmdepths = map n (map maxMdepth (snd (giants t)))
maxmDdepths = map n (map maxMdepth (map dual (snd (giants t))))

maxTdepths = map n (map maxTdepth (snd (giants t)))
maxTDdepths = map n (map maxTdepth (map dual (snd (giants t))))

hd x = fst (decons x)

tl x = snd (decons x)

decons a | even_ a = (s x,hf (s' xs)) where (x,xs) = c' a
decons a = (e,hf (s' a))

cons (x,y) = leftshiftBy x (s (db y))

syracuse :: Cat b => b -> b
syracuse n = tl (add n (db (s n)))

nsyr :: Cat t => t -> [t]
nsyr x | e_ x = [e]
nsyr x = x : nsyr (syracuse x)

-- misc

to_bin :: Cat a => a->[Int]
to_bin x = f b xs where
  xs = map s (to_list x)
  b = (length xs) `mod` 2
  f _ [] = []
  f b (x:xs)  = rep x b (f (1-b) xs)

rep :: Cat a => a -> a1 -> [a1] -> [a1]
rep k a as | e_ k = as
rep k a as = a:rep (s' k) a as
  
len :: Cat a => [a] -> a  
len [] = e
len (_:xs) = s (len xs) -- asTypeOf (s (len xs) x)

-- latex formula

l :: Cat a=>a->String
l x | e_ x = "0"
l a | even_ a = "{(2^"++(l1 x)++(l y)++")}" where
   (x,y) = c' a 
l z | e_ y = "{(2^{"++(l1 x)++"}-1)}" where
    (x,y) = c' z
l a ="{(2^"++(l1 x)++(l1 y)++"-1)}" where
  (x,y) = c' a 

l1 :: Cat a => a -> String
l1 x = "{"++(l x)++"+1}"

tx t = mapM_ print (map t [0..15])


-- op2 f x y = view (f (n x) (n y))


