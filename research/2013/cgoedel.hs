module Goedel where
import Data.List
import Data.Char

type N = Integer

binomial :: N->N->N

binomial n k | n<k = 0
binomial _ k | k<0 = 0
binomial n k = binomialLoop (min k (n-k)) 0 1 where
  binomialLoop k i p | i >= k = p
  binomialLoop k i p = 
    binomialLoop k (i+1) ((n - i) * p `div` (i+1))

list2set xs = tail (scanl f (-1) xs) where f x y = x+y+1

set2list ms = zipWith g ms (-1:ms) where g x y = x-y-1

fromCantorTuple ns = fromKSet (list2set ns)

fromKSet xs = sum (zipWith binomial xs [1..])

binomialDigits :: N->N->[N]
binomialDigits 0 _ = []
binomialDigits k n | k > 0 = 
    (m-1) : binomialDigits (k-1) (n-bdigit) where
      m = upperBinomial k n
      bdigit = binomial (m-1) k

upperBinomial :: N->N->N
upperBinomial k n = binarySearch l m where
  m = roughLimit k (n+k) k
  l = m `div` 2
  
  binarySearch from to | from==to = from 
  binarySearch from to = 
    if binomial mid k > n 
      then binarySearch from mid
      else binarySearch (mid+1) to where 
        mid = (from + to) `div` 2
        
  roughLimit k n i | binomial i k > n = i
  roughLimit k n i = roughLimit k n (2*i)

toCantorTuple k n = set2list (toKSet k n)

toKSet k n = reverse (binomialDigits k n)

toBijBase :: N->N->[N]
toBijBase _ 0 = []
toBijBase b n | n>0 = d : ds where
  (d,m) = getBijDigit b n
  ds = toBijBase b m

fromBijBase :: N->[N]->N  
fromBijBase _ [] = 0
fromBijBase b (d:ds) = n where
  m = fromBijBase b ds
  n = putBijDigit b d m  

getBijDigit :: N->N->(N,N)  
getBijDigit b n | n>0 = if d == 0 then (b-1,q-1) else (d-1,q) where
     (q,d) = quotRem n b

putBijDigit :: N->N->N->N
putBijDigit b d m | 0 <= d && d < b = 1+d+b*m  

knat2nats _ 0 = []
knat2nats _ 1 = [0]
knat2nats k n | n>0 = ns where 
  n' = pred n
  k' = succ k
  xs = toBijBase k' n' 
  nss = splitWith k xs
  ns = map (fromBijBase k) nss

  splitWith sep xs =  y : f ys where
   (y, ys) = break (==sep) xs

   f [] = []
   f (_:zs) = splitWith sep zs

knats2nat _ [] = 0
knats2nat _ [0] = 1
knats2nat k ns = n where
  nss = map (toBijBase k) ns
  xs = intercalate [k] nss 
  n' = fromBijBase (succ k) xs
  n = succ n'

bbase = 3

nat2nats n = knat2nats bbase n
nats2nat n = knats2nat bbase n

data Term var const = 
   Var var | Fun const [Term var const] 
     deriving (Eq,Show,Read)

nterm2code :: Term N N -> N

nterm2code (Var i) = 2*i
nterm2code (Fun cName args) = code where
  cs = map nterm2code args
  fc = nats2nat (cName:cs)
  code = 2*fc-1

code2nterm :: N -> Term N N

code2nterm n | even n = Var (n `div` 2) 
code2nterm n = Fun cName args where
  k = (n+1) `div` 2
  cName:cs = nat2nats k
  args = map code2nterm cs

c0='a'
c1='z'

base = 1+ord c1-ord c0

string2nat :: String -> N
string2nat cs = fromBijBase (fromIntegral base) 
  (map (fromIntegral . chr2ord) cs)

nat2string :: N -> String
nat2string n | n >= 0 = map (ord2chr . fromIntegral) 
  (toBijBase (fromIntegral base) n)

chr2ord c | c>=c0 && c<=c1 = ord c - ord c0
ord2chr o | o>=0 && o<base = chr (ord c0+o)

sterm2code :: Term N String -> N

sterm2code (Var i) = 2*i
sterm2code (Fun name args) = 2*fc-1 where
  cName = string2nat name
  cs = map sterm2code args
  fc = nats2nat (cName:cs)

code2sterm :: N -> Term N String

code2sterm n | even n = Var (n `div` 2) 
code2sterm n = Fun name args where
  k = (n+1) `div` 2
  cName:cs = nat2nats k
  name = nat2string cName
  args = map code2sterm cs

data FTerm a b c = V a | C b | F c [FTerm a b c] 
                   deriving (Eq,Read,Show)

term2nat vars consts funs t | lv+lc>0 && lf>0 = 
 encode t where
  lv = genericLength vars
  lc = genericLength consts
  lf = genericLength funs
  
  encode (V x) = n where n = indexOf x vars
  encode (C c) = lv+n where n = indexOf c consts
  encode (F f xs) = n where 
    d = indexOf (f,k) funs
    k = genericLength xs
    ns = map encode xs
    m = fromCantorTuple ns
    n' = putBijDigit lf d m 
    n = n'+lv+lc-1  

  indexOf x (y:xs) | x==y = 0
  indexOf x (_:xs) = 1 + indexOf x xs

nat2term vars consts funs n | lv+lc>0 && lf>0 = 
 decode n where
  lv = genericLength vars
  lc = genericLength consts
  lf = genericLength funs
  
  decode n | 0<=n && n < lv = 
    V (vars `genericIndex` n)
  decode n | lv <=n && n < lc+lv = 
    C (consts `genericIndex` (n-lv))
  decode n | lc+lv<=n = F f (map decode ns) where 
    n' = 1+n-(lc+lv)
    (d,m) = getBijDigit lf n'
    (f,k) = funs `genericIndex` d
    ns = toCantorTuple k m

vars = ["x","y","z"]
consts = [0,1]
funs = [("~",1),("*",2),("+",2),("if",3)]

t2n :: FTerm String Integer String -> N
t2n = term2nat vars consts funs

n2t :: N -> FTerm String Integer String
n2t = nat2term vars consts funs

tshow t = toString t where
  s x = filter (/='"') (show x)
  toString (V x) = s x
  toString (C c) = s c
  toString (F f (x:y:[])) = 
    "("++(toString x) ++ " " ++ s f ++ " " ++ (toString y)++")"
  toString (F f xs) = s f ++ "("++zs++")" where
    ys = map toString xs
    zs = intercalate "," ys

