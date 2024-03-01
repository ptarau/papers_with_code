module CycArith where
import Data.List

maxint = 100

partitions n = ps 1 n where
      ps x 0 = [[]]
      ps x y = [t:ts | t <- [x..y], ts <- ps t (y - t)]


landau n =  m where
  ps = partitions n
  ls = map (foldl lcm 1) ps
  zs = zip ls ps
  m = foldl1 cmp zs where
    cmp (x,_) (y,ys) | x < y = (y,ys)
    cmp (x,xs) _ = (x,xs)

lans n = landau (i+1) where
  f (k,_xs) = k<n
  is = [0..]
  ls = takeWhile f (map landau is)
  ps = zip [0..] ls
  (i,_)=last ps

pris 0 = (1,[])
pris 1 = (1,[1])
pris n = (product rs,sort rs) where
  ps = tail primes
  xs = takeWhile (<n) (scanl (*) 1 ps)
  m = last xs
  es = map (2^) [0..]
  ys = takeWhile (<n) (zipWith (*) es (repeat m))
  rs = 2^(length ys):take (length xs-1) ps -- primorials

makeGenerator f n =   pss where
  psum xs = scanl (+) 0 xs 
  toCycle from to = [from..to-1]   
  (p:ps) =  psum (snd (f n))
  pss = zipWith toCycle (p:ps) ps

lGenerator = makeGenerator lans
pGenerator = makeGenerator pris    

generator = pGenerator maxint

isGenerator x = x==generator

cycTemplate = pris maxint

s xss = map rrot xss

rrot [] = []
rrot (x:xs) = xs ++ [x]

s' xss = map lrot xss

lrot [] = []
lrot xs = last xs : (init xs)

n2p 0 = generator
n2p n | n >0 = s (n2p (n-1))

p2n z | isGenerator z = 0
p2n x = 1+p2n (s' x)

slowAdd x y | isGenerator x = y
slowAdd x y = s (slowAdd (s' x) y)

z ds = zipWith f bs ds where
  bs = snd cycTemplate
  f b d = (d+1) `mod` b

z' ds = zipWith f bs ds where
  bs = snd cycTemplate
  f b d = (d'-1) `mod` b where 
    d' = if d==0 then b else d

zZero = replicate (length (snd cycTemplate)) 0

n2zs n = iter z zZero n

zs2n zs | zs == zZero = 0
zs2n zs = 1+ zs2n (z' zs) 

zOrbit = nub r where 
  m=fst cycTemplate
  l=length (snd cycTemplate)
  r =  map n2zs [0..m-1]

iter _ x 0 = x
iter f x k = f (iter f x (k-1))   

n2ps n = iter s generator n

sOrbit = nub r where 
  m=fst cycTemplate
  r =  map n2ps [0..m-1]

permTest = mapM_ print sOrbit
znTest =   mapM_ print zOrbit

zs2n' zs | ok = crt zs bs where
  bs = snd cycTemplate
  ok = and (zipWith (<) zs bs)  
  
n2zs' n | n<m = map f bs where
  (m,bs) = cycTemplate
  f b = n `mod` b

zs2cp xs  =   zipWith rotR xs generator

rotR k xs | k<=genericLength xs && k>=0 = 
  (genericDrop k xs) ++  (genericTake k xs)
rotL k xs = rotR (genericLength xs-k) xs

cp2zs xss = map f xss where f xs = findElem (maximum xs) (reverse xs)
   
findElem x (y:xs) = if x==y then 0 else 1+findElem x xs  

n2cp n = (zs2cp . n2zs') n

cp2n xss  = (zs2n' . cp2zs) xss 

zsOp op  xs ys = zipWith3 f bs xs ys where
  bs = snd cycTemplate
  f b x y = (op x y) `mod` b

zsAdd  xs ys = zsOp (+) xs ys

zsMul  xs ys = zsOp (*) xs ys

cpOp op  xss yss = zs2cp (zsOp op (cp2zs xss) (cp2zs yss))

cpAdd xss yss = cpOp (+) xss yss

cpMul xss yss = cpOp (*) xss yss

get_bdigit b n | n>0 = 
  if d == 0 then (b-1,q-1) else (d-1,q) where
     (q,d) = quotRem n b

put_bdigit b d m | 0 <= d && d < b = 1+d+b*m

toBaseList bs n  = f bs (skip+n) where
  skip = sum (init (scanl (*) 1 bs))
  f []  0 = []
  f(b:bs) n = d:ds where
    (d,m)=get_bdigit b n
    ds = f bs m

fromBaseList bs xs = (f bs xs)-skip where
  skip = sum (init (scanl (*) 1 bs))
  f [] [] = 0
  f (b:bs) (x:xs) = put_bdigit b x (f bs xs)

primes = 2 : filter is_prime [3,5..]

is_prime p = [p]==to_primes p

to_primes n|n>1 = 
  to_factors n p ps where (p:ps) = primes

to_factors n p ps | p*p > n = [n]
to_factors n p ps | 0==n `mod` p = 
  p : to_factors (n `div` p)  p ps 
to_factors n p ps@(hd:tl) = to_factors n hd tl

crt :: [Integer]->[Integer]->Integer
crt as ns  = head (dropWhile(<0) [s,s+prod..]) where
    s = sum [ div (x*y*prod) z | (x,y,z)<- zip3 as ls ns ]
    prod = abs(product ns)
    ls = [extended_gcd x (div prod x) !! 1 |x<- ns]

extended_gcd:: Integer->Integer->[Integer]
extended_gcd a b | mod a b == 0 = [0,1,b]
extended_gcd a b = [y,x-y*(a `div` b),z] where
  [x,y,z] = extended_gcd b (mod a b)

