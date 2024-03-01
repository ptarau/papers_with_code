module SharedAxioms where
import Data.List
import Data.Bits
import Test.QuickCheck

import CPUTime

data OIs = E | O OIs | I OIs deriving (Eq, Show, Read)

empty = E

withO xs = O xs  
withI xs = I xs

reduce (O xs) = xs
reduce (I xs) = xs

isEmpty xs = xs == E

isO (O _) = True
isO _     = False

isI (I _) = True
isI _     = False

zero = empty
one = withO empty  
  
peanoSucc xs | isEmpty xs = one
peanoSucc xs | isO xs = withI (reduce xs)
peanoSucc xs | isI xs = withO (peanoSucc (reduce xs)) 

class (Eq n,Read n,Show n)=>Polymath n where  
  e :: n 
  o_ :: n -> Bool
  o :: n -> n 
  i :: n -> n
  r :: n -> n

  e_ :: n -> Bool
  e_ x = x == e

  i_ :: n -> Bool
  i_ x = not (o_ x || e_ x)

  u :: n
  u = o e
  
  u_ :: n -> Bool
  u_ x = o_ x && e_ (r x)

  s, p :: n -> n
  
  s x | e_ x = u
  s x | o_ x = i (r x)
  s x | i_ x = o (s (r x)) 
  
  p x | u_ x = e
  p x | o_ x = i (p (r x)) 
  p x | i_ x = o (r x)

view :: (Polymath a,Polymath b)=>a -> b
view x | e_ x = e
view x | o_ x = o (view (r x))
view x | i_ x = i (view (r x))

allFrom k = k : allFrom (s k)

prop_poly :: Polymath a => a -> Bool
prop_poly x  = 
  r (o x) == x && r (i x) == x &&
  e_ (e `withType` x) && o_ (o x) && i_ (i x) &&
  exactlyOneOf [e_ x, o_ x, i_ x] where

  exactlyOneOf xs = length [ x | x <- xs, x ] == 1

prop_iso :: (Polymath a, Polymath b) => a -> b -> Bool
prop_iso x y =  
  view (view x `withType` y) == x &&
  view (view y `withType` x) == y 

withType :: a -> a -> a
x `withType` y = x

arbitraryPolymath :: Polymath a => Gen a
arbitraryPolymath =
  oneof [return e,
         fmap o arbitraryPolymath,
         fmap i arbitraryPolymath]

newtype N = N Integer deriving (Eq,Show,Read)

instance Polymath N where
  e = N 0
  o_ (N x) = odd x
  o  (N x) = N (2*x+1)
  i  (N x) = N (2*x+2)
  r  (N x) | x >  0 = N ((x-1) `div` 2)

instance Arbitrary N where arbitrary = arbitraryPolymath

data Peano = Zero|Succ Peano deriving (Eq,Show,Read)

instance Polymath Peano where
  e = Zero
  
  o_ Zero = False
  o_ (Succ x) = not (o_ x) 
  
  o x = Succ (o' x) where
    o' Zero = Zero
    o' (Succ x) = Succ (Succ (o' x))
    
  i x = Succ (o x)
  
  r (Succ Zero) = Zero
  r (Succ (Succ Zero)) = Zero
  r (Succ (Succ x)) = Succ (r x) 

instance Arbitrary Peano where 
  arbitrary = arbitraryPolymath
  
prop_Peano :: Peano -> Bool
prop_Peano x  =  Succ x == s x && 
  (x == Zero || Succ (p x) == x)  

test_Peano = quickCheck prop_Peano >>
             quickCheck (prop_poly :: Peano -> Bool)

instance Polymath OIs where
  e=empty
  o=withO
  o_=isO 
  i=withI
  r=reduce

instance Arbitrary OIs where
  arbitrary = arbitraryPolymath

data S=S [S] deriving (Eq,Read,Show)

ackermann :: S -> Integer
ackermann (S xs) = sum (map ((2^) . ackermann) xs) 

isAscending :: [S] -> Bool
isAscending []  =  True
isAscending [x]  =  ackermann x >=0
isAscending (x:y:zs)  =  0 <= ackermann x && 
  ackermann x < ackermann y && isAscending (y:zs)

canonicalSet :: S->Bool
canonicalSet (S []) = True
canonicalSet (S xs) = 
  (all canonicalSet xs) && (isAscending xs)

instance Arbitrary S where
  arbitrary = arbitraryPolymath

instance Polymath S where
  e = S []
  
  o_ (S (S []:_)) = True
  o_ _ = False
  
  o (S xs) = s (S (map s xs))
  
  i = s . o

  s (S xs) = S (lift (S []) xs) where
 
  p (S (x:xs)) = S (lower x xs) where
     
  r (S xs) = S (map p (adjust (p (S xs)))) where 

lift k (x:xs) | k == x = lift (s x) xs
lift k xs = k:xs

lower (S []) xs = xs
lower k xs = lower (p k) (p k:xs)

adjust (S (S []:xs)) = xs
adjust (S xs) = xs
    

prop_lift (S []) = True
prop_lift (S (x:xs)) = lift e ((e `upto` x) ++ xs) == x : xs

prop_lower (S []) = True
prop_lower (S (x:xs)) = lower x xs == (e `upto` x) ++ xs

x `upto` y | x == y  = []
x `upto` y = x : (s x `upto` y)

test_S = quickCheck canonicalSet >>
         quickCheck prop_lift >>
         quickCheck prop_lower >>
         quickCheck (prop_poly :: S -> Bool) >>
         quickCheck (prop_iso :: OIs -> S -> Bool)

data F = F [F] deriving (Eq,Read,Show)

diffs []  =  []
diffs (x:xs)  =  x : dffs x xs where
  dffs x []  =  []
  dffs x (y:ys)  =  y-x-1 : dffs y ys

sums []  =  []
sums (x:xs)  =  x : sms x xs where
  sms x []      =  []
  sms x (y:ys)  =  x+y+1 : sms (x+y+1) ys

prop_diffs :: [Integer] -> Bool
prop_diffs xs  =  sums (diffs xs) == xs && diffs (sums xs) == xs

test_diffs = quickCheck prop_diffs

instance Polymath F where 
  e = F []
  
  o_ (F (F []:_)) = True
  o_   _          = False
  
  o (F xs) = F (e:xs)

  i (F xs) = s (F (e:xs))

  s (F xs) = F (hinc xs) where
    hinc ([]) = [e]
    hinc (x : xs) | e_ x = s k : ys where 
      (k : ys) = hinc xs 
    hinc (k : xs) = e : p k : xs

  p (F xs) = F (hdec xs) where
    hdec [x] | e_ x = []
    hdec (x : k : xs) | e_ x = s k : xs
    hdec (k : xs) = e : hdec (p k : xs)
    
  r (F (x : xs)) | e_ x = F xs
  r (F (k : xs)) = F (hpad (p k) (hnext xs)) where
    hpad x xs | e_ x = xs
    hpad x xs = e : hpad (p x) xs
  
    hnext [] = []
    hnext (k : xs) = s k : xs

class (Polymath n) => PolyOrdering n where
  lcmp :: n -> n -> Ordering
  lcmp x y | e_ x && e_ y = EQ 
  lcmp x y | e_ x && not(e_ y) = LT
  lcmp x y | not(e_ x) && e_ y = GT
  lcmp x y = lcmp (r x) (r y)

  cmp :: n -> n -> Ordering
  cmp x y = ecmp (lcmp x y) x y where
     ecmp EQ x y = samelen_cmp x y
     ecmp b _ _ = b
     
  samelen_cmp :: n -> n -> Ordering

  samelen_cmp x y | e_ x && e_ y = EQ
  samelen_cmp x y | e_ x && not(e_ y) = LT
  samelen_cmp x y | not(e_ x) && e_ y = GT
  samelen_cmp x y | o_ x && o_ y = samelen_cmp (r x) (r y)
  samelen_cmp x y | i_ x && i_ y = samelen_cmp (r x) (r y)
  samelen_cmp x y | o_ x && i_ y = 
    downeq (samelen_cmp (r x) (r y)) where
      downeq EQ = LT
      downeq b = b
  samelen_cmp x y | i_ x && o_ y = 
    upeq (samelen_cmp (r x) (r y)) where
      upeq EQ = GT
      upeq b = b

  lt, gt, eq :: n -> n -> Bool
  
  lt x y = LT == cmp x y
  gt x y = GT == cmp x y
  eq x y = EQ == cmp x y

  nsort :: [n] -> [n]
  nsort ns = sortBy cmp ns

  bitlen :: n -> n
  bitlen x | e_ x = e
  bitlen x = s (bitlen (r x))

  oS :: n -> n
  oS l | e_ l = e
  oS l = o (oS (p l))

  iS :: n -> n
  iS l | e_ l = e
  iS l = i (iS (p l))

  isGalois :: (n -> n) -> (n -> n) -> n -> n -> Bool
  isGalois f g x y = v1 == v2 where
    v1=le (f x) y
    v2=le x (g y)
  
  isGaloisAnti :: (n -> n) -> (n -> n) -> n -> n -> Bool
  isGaloisAnti f g x y = v1 == v2 where
    v1=le (f x) y
    v2=le (g y) x
      
  le :: n -> n -> Bool  
  le a b = not (lt b a)

instance PolyOrdering N
instance PolyOrdering Peano
instance PolyOrdering OIs
instance PolyOrdering S
instance PolyOrdering F

class (PolyOrdering n) => PolyArithmetic n where
  a :: n -> n -> n 
  
  a x y | e_ x = y
  a x y | e_ y = x
  a x y | o_ x && o_ y =    i (a (r x) (r y))
  a x y | o_ x && i_ y = o (s (a (r x) (r y)))
  a x y | i_ x && o_ y = o (s (a (r x) (r y)))
  a x y | i_ x && i_ y = i (s (a (r x) (r y)))

  d :: n -> n -> n 

  d x y | e_ x && e_ y = e
  d x y | not(e_ x) && e_ y = x
  d x y | not (e_ x) && x == y = e
  d z x | i_ z && o_ x = o (d (r z) (r x))  
  d z x | o_ z && o_ x = i (d (r z) (s (r x)))  
  d z x | o_ z && i_ x = o (d (r z) (s (r x)))
  d z x | i_ z && i_ x = i (d (r z) (s (r x)))  

  m :: n -> n -> n
  m x _ | e_ x = e
  m _ y | e_ y = e
  m x y = s (m0 (p x) (p y)) where
    m0 x y | e_ x = y
    m0 x y | o_ x = o (m0 (r x) y)
    m0 x y | i_ x = s (a y  (o (m0 (r x) y)))
  
  double,half :: n -> n
  
  double = p . o
  half = r . s

  exp2 :: n -> n
  exp2 x | e_ x = u
  exp2 x = double (exp2 (p x)) 

instance PolyArithmetic N
instance PolyArithmetic Peano
instance PolyArithmetic OIs
instance PolyArithmetic S
instance PolyArithmetic F

class (PolyArithmetic n) => PolyPair n where
  pair :: n -> n -> n
  pair x y = h x (double y) where
    h x ys | e_ x = ys
    h x ys = o  (h (p x) ys)
  
  first, second :: n -> n
  
  first z | o_ z = s (first (half z))
  first _ = e

  second z = half (t z) where
    t xs | o_ xs = t (half xs)
    t xs  = xs

instance PolyPair N
instance PolyPair Peano
instance PolyPair OIs
instance PolyPair S
instance PolyPair F

class (PolyPair n) => PolyCollection n where
  as_mset_list :: [n] -> [n]  
  as_mset_list ns = tail (scanl a e ns)
  
  as_list_mset :: [n] -> [n]
  as_list_mset ms = 
    zipWith d ms' (e: ms') where ms'=nsort ms

  as_set_list :: [n] -> [n]
  as_set_list = (map p) . as_mset_list . (map s)
  
  as_list_set :: [n] -> [n]
  as_list_set = (map p) . as_list_mset . (map s)  

instance PolyCollection N
instance PolyCollection Peano
instance PolyCollection OIs
instance PolyCollection S
instance PolyCollection F

class (PolyCollection n) => PolyCons n where
  hd, tl ::  n -> n
  
  hd = first . p
  tl = second . p
  
  cons :: n -> n -> n
  cons x y = s (pair x y)
  
  as_list_nat :: n -> [n]
  as_list_nat x | e_ x = []
  as_list_nat x = hd x : as_list_nat (tl x)
 
  as_nat_list :: [n] -> n  
  as_nat_list [] = e
  as_nat_list (x:xs) = cons x (as_nat_list xs)

  as_nat_set :: [n] -> n
  as_nat_set = as_nat_list . as_list_set
  
  as_set_nat :: n -> [n]
  as_set_nat = as_set_list . as_list_nat

  as_nat_mset :: [n] -> n
  as_nat_mset = as_nat_list . as_list_mset
  
  as_mset_nat :: n -> [n]
  as_mset_nat = as_mset_list . as_list_nat

  treeSize :: n -> n
  treeSize x | e_ x=e
  treeSize x = s (a (treeSize (hd x)) (treeSize (tl x)))

  pow :: n -> n -> n
  pow _ y | e_ y = u
  pow x _ | e_ x = e 
  pow x y = z where
    b=pow2n x (hd y)
    b'=pow b (tl y)
    z=m b (m b' b')
 
    pow2n x n | e_ n = x
    pow2n x n = pow2n (m x x) (p n) 

instance PolyCons N
instance PolyCons Peano
instance PolyCons OIs
instance PolyCons S
instance PolyCons F

class (PolyCons n) => PolySet n where
  setOp2 :: ([n] -> [n] -> [n]) -> (n -> n -> n)
  setOp2 op x y = as_nat_set 
    (op (as_set_nat x) (as_set_nat y))

  setIntersection,setUnion,setDifference :: n -> n -> n
  
  setIntersection = setOp2 intersect            
  setUnion = setOp2 union
  setDifference = setOp2 (\\)
  
  setIncl :: n -> n -> Bool
  setIncl x y = x == (setIntersection x y)

  powset :: n -> n
  powset x = as_nat_set 
    (map as_nat_set (subsets (as_set_nat x))) where
      subsets [] = [[]]
      subsets (x:xs) = [zs|ys<-subsets xs,zs<-[ys,(x:ys)]]   

  inSet :: n -> n -> Bool
  inSet x y = setIncl (as_nat_set [x]) y 
  
  augment :: n -> n
  augment x = setUnion x (as_nat_set [x])

  nthOrdinal :: n -> n
  nthOrdinal x | e_ x = e
  nthOrdinal n = augment (nthOrdinal (p n)) 

instance PolySet N
instance PolySet Peano
instance PolySet OIs
instance PolySet S
instance PolySet F

class (PolySet n) => PolyList n where
  listOp1 :: ([n] -> [n]) -> (n -> n)
  listOp1 f = as_nat_list . f . as_list_nat 
  listOp2 :: ([n] -> [n] -> [n]) -> (n -> n -> n)
  listOp2 op x y = as_nat_list 
    (op (as_list_nat x) (as_list_nat y))

  listConcat :: n -> n -> n
  listConcat = listOp2 (++)
                   
  listReverse :: n -> n
  listReverse = listOp1 reverse

  listFoldr :: (n -> n -> n) -> n -> n -> n
 
  listFoldr f z xs | e_ xs = z
  listFoldr f z xs = f (hd xs) (listFoldr f z (tl xs))

  listConcat' :: n -> n -> n
  listConcat' xs ys = listFoldr cons ys xs 
  
  listSum :: n -> n
  listSum = listFoldr a u
  
  listProduct :: n -> n
  listProduct = listFoldr m u

instance PolyList N
instance PolyList Peano
instance PolyList OIs
instance PolyList S
instance PolyList F

class (PolyList n) => PolyGraph n where

  ordUnpair, unordUnpair, upwardUnpair :: n -> (n,n)
  ordPair, unordPair, upwardPair :: (n,n) -> n
  
  ordUnpair z = (first z,second z)
  
  ordPair (x,y) = pair x y

  unordUnpair z = (x',y') where 
    (x,y) = ordUnpair z
    [x',y'] = as_mset_list  [x,y]
    
  unordPair (x,y) = ordPair (x',y') where 
    [x',y'] = as_list_mset [x,y]

  upwardUnpair z = (x',y') where 
    (x,y) = ordUnpair z
    [x',y'] = as_set_list [x,y]
    
  upwardPair (x,y) = ordPair (x',y') where 
    [x',y'] = as_list_set [x,y]

  as_set_digraph :: [(n,n)] -> [n]
  as_set_digraph = map ordPair
  
  as_digraph_set :: [n] -> [(n,n)]
  as_digraph_set = map ordUnpair

  as_set_graph :: [(n,n)] -> [n]
  as_set_graph = map unordPair
  
  as_graph_set :: [n] -> [(n,n)]
  as_graph_set = map unordUnpair

  as_set_dag :: [(n,n)] -> [n]
  as_set_dag  = map upwardPair
  
  as_dag_set :: [n] -> [(n,n)]
  as_dag_set = map upwardUnpair

  as_hypergraph_set :: [n] -> [[n]]
  as_hypergraph_set = map (as_set_nat . s)
  
  as_set_hypergraph :: [[n]] -> [n]
  as_set_hypergraph = map (p . as_nat_set)

instance PolyGraph N
instance PolyGraph Peano
instance PolyGraph OIs
instance PolyGraph S
instance PolyGraph F
instance PolyGraph Integer

infixr 5 :->
data T = T|T :-> T deriving (Eq, Read, Show)

instance Polymath T where
  e = T
 
  o_ (T :-> x ) = True
  o_ _       = False
 
  o x = T :-> x
  i x = s (T :-> x)

  r (T :-> y) = y
  r (x :-> y) = hpad (p x) y where  
    hpad T y = hnext y
    hpad x y = T :-> hpad (p x) y
    hnext T = T
    hnext (x :-> y) = s x :-> y 

  s T = T :-> T
  s (T :-> y) = s x :-> y' where x :-> y' = s y
  s (x :-> y) = T :-> (p x :-> y) 
 
  p (T :-> T) = T
  p (T :-> (x :-> y)) = s x :-> y
  p (x :-> y) = T :-> p (p x :-> y)

instance PolyOrdering T
instance PolyCollection T
instance PolyArithmetic T
instance PolyPair T
instance PolyCons T
instance PolySet T
instance PolyList T
instance PolyGraph T

instance Polymath Integer where
  e = 0
  o_ x = testBit x 0
 
  o x = succ (shiftL x 1) 
  i  = succ . o
  r x | x>0 = shiftR (pred x) 1

  s = succ
  p n | n>0 = pred n
  
  u = 1
  u_ = (== 1)
  
instance PolyOrdering Integer where
  lt = (<)
  nsort = sort
  cmp=compare

instance PolyCollection Integer
instance PolyArithmetic Integer where
  d x y | x<=y = x-y
  m = (*)
  half x = shiftR x 1
  double x = shiftL x 1
  
instance PolyPair Integer  
instance PolyCons Integer

instance PolySet Integer where
  setUnion = (.|.)
  setIntersection = (.&.)
  setDifference x y = x .&. (complement y)
  
  inSet x xs = testBit xs (fromIntegral x)
 
  powset 0 = 1
  powset x = xorL (powset (pred x)) where
    xorL n = n `xor` (shiftL n 1)
  
instance PolyList Integer

powset' i = product (map (\k -> 1+2^(2^k)) (as_set_nat i)) 

syracuse n = tl (a (m six n) four) where 
  four = s (s (s (s e)))
  six = s (s four)

nsyr n | e_ n = [e]
nsyr n = n : nsyr (syracuse n)

cs::[Integer]
cs=[1234567890,12345678901234567890,   
    123456789012345678901234567890
    --,123456789012345678901234567890123456789012345678901234567890
    ]

bm = do     
       i<-bmI
       print i
       k<-bmK
       print k
       t<-bmT
       print t
       n<-bmN
       print n
       f<-bmF
       print f
       s<-bmS
       print s
       return []

bmI = bmx "I" cI
bmK = bmx "OIs" cK
bmT = bmx "T" cT
bmN = bmx "N" cN
bmF = bmx "F" cF
bmS = bmx "S" cS

cI c = c :: Integer
cK c=view (c :: Integer) :: OIs 
cT c=view (c :: Integer) :: T
cN c=view (c :: Integer) :: N 
cF c=view (c :: Integer) :: F
cS c=view (c :: Integer) :: S


bmx s f = mapM (benchmark s.f) cs
 
benchmark s n = do
  x<-getCPUTime
  print (sumsyr 100 n) 
  y<-getCPUTime
  let t=(y-x) `div` 1000000000
  return (s++": time="++(show t))
 
benchmark1 k a b = do
  x<-getCPUTime
  print (m (kpows k a b) e)
  y<-getCPUTime
  let t=(y-x) `div` 1000000000
  return ("time="++(show t))  

kpows k n x = foldr a e (map f (take k (allFrom n))) where
  f b = pow b x

bm1 = bm1x 10 100 100

bm1x :: Int -> Integer -> Integer -> IO [Char]
bm1x k a b = do
        i<-benchmark1 k (view a::Integer) (view b :: Integer)
        print i
        ois<-benchmark1 k (view a::OIs) (view b :: OIs)
        print ois
        t<-benchmark1 k (view a::T) (view b :: T)
        print t
        n<-benchmark1 k (view a::N) (view b :: N)
        print n
        f<-benchmark1 k (view a::F) (view b :: F)
        print f
        s<-benchmark1 k (view a::S) (view b :: S)
        print s
        return "done"
      

sumsyr k n = sum (map (length.nsyr) (take k (allFrom n)))

