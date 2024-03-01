module RCN where
import System.Random

data T = F [T] deriving (Eq,Show,Read)

odd_ ::  T -> Bool
odd_ (F []) = False
odd_ (F (_:xs)) = even_ (F xs)

even_ :: T -> Bool
even_ (F []) = True
even_ (F (_:xs)) = odd_ (F xs)

type N = Integer

n :: T -> N
n (F []) = 0
n a@(F (x:xs)) | even_ a = 2^(n x + 1)*(n (F xs))
n a@(F (x:xs)) | odd_ a = 2^(n x + 1)*(n (F xs)+1)-1

t :: N -> T
t 0 = F []
t k | k>0 = F zs where
  (x,y) = split_on (parity k) k
  F ys = t y
  zs = if x==0 then ys else t (x-1) : ys

  parity x = x `mod` 2

  split_on b z | z>0 && parity z == b = (1+x,y) where
    (x,y) = split_on b  ((z-b) `div` 2)
  split_on _ z = (0,z)

s :: T -> T
s (F []) = F [F []] -- 1
s (F [x]) = F [x,F []] -- 2

s a@(F (F []:x:xs)) | even_ a = F (s x:xs) -- 3
s a@(F (x:xs)) | even_ a = F (F []:s' x:xs) -- 4

s a@(F (x:F []:y:xs)) | odd_ a = F (x:s y:xs) -- 5
s a@(F (x:y:xs)) | odd_ a = F (x:F []:(s' y):xs) -- 6

s' :: T -> T
s' (F [F []]) = F [] -- 1
s' (F [x,F []]) = F [x] -- 2

s' b@(F (x:F []:y:xs)) | even_ b = F (x:s y:xs) -- 6
s' b@(F (x:y:xs)) | even_ b = F (x:F []:s' y:xs) -- 5

s' b@(F (F []:x:xs)) | odd_ b = F (s x:xs) -- 4
s' b@(F (x:xs)) | odd_ b = F (F []:s' x:xs) -- 3

db :: T -> T
db (F []) = F []
db a@(F xs) | odd_ a = F (F []:xs)
db a@(F (x:xs)) | even_ a = F (s x:xs)

hf :: T -> T
hf (F []) = F []
hf (F (F []:xs)) = F xs
hf (F (x:xs)) = F (s' x:xs)

exp2 :: T -> T
exp2 (F []) = F [F []]
exp2 x = F [s' x,F []]

log2 :: T -> T
log2 (F [F []]) = F []
log2 (F [y,F []]) = s y

leftshiftBy :: T -> T -> T
leftshiftBy (F []) k = k
leftshiftBy _ (F []) = F []
leftshiftBy x k@(F xs) | odd_ k = F ((s' x):xs)
leftshiftBy x k@(F (y:xs)) | even_ k = F (add x y:xs)

leftshiftBy' :: T -> T -> T
leftshiftBy' x k = s' (leftshiftBy x (s k))

leftshiftBy'' :: T -> T -> T
leftshiftBy'' x k = s' (s' (leftshiftBy x (s (s k))))

add :: T -> T -> T
add (F []) y = y
add x (F []) = x

add x@(F (a:as)) y@(F (b:bs)) |even_ x && even_ y = f (cmp a b) where
  f EQ = leftshiftBy (s a) (add (F as) (F bs))
  f GT = leftshiftBy (s b)
    (add (leftshiftBy (sub a b) (F as)) (F bs))
  f LT = leftshiftBy (s a)
    (add (F as) (leftshiftBy (sub b a) (F bs)))

add x@(F (a:as)) y@(F (b:bs)) |even_ x && odd_ y = f (cmp a b) where
  f EQ = leftshiftBy' (s a) (add (F as) (F bs))
  f GT = leftshiftBy' (s b)
    (add (leftshiftBy (sub a b) (F as)) (F bs))
  f LT = leftshiftBy' (s a)
    (add (F as) (leftshiftBy' (sub b a) (F bs)))

add x y |odd_ x && even_ y = add y x

add x@(F (a:as)) y@(F (b:bs)) | odd_ x && odd_ y = f (cmp a b) where
  f EQ =  leftshiftBy'' (s a) (add (F as) (F bs))
  f GT =  leftshiftBy'' (s b)
    (add (leftshiftBy' (sub a b) (F as)) (F bs))
  f LT =  leftshiftBy'' (s a)
    (add (F as) (leftshiftBy' (sub b a) (F bs)))

sub :: T -> T -> T
sub x (F []) = x
sub x@(F (a:as)) y@(F (b:bs)) | even_ x && even_ y = f (cmp a b) where
  f EQ = leftshiftBy (s a) (sub (F as) (F bs))
  f GT = leftshiftBy (s b)
    (sub (leftshiftBy (sub a b) (F as)) (F bs))
  f LT = leftshiftBy (s a)
    (sub (F as) (leftshiftBy (sub b a) (F bs)))

sub x@(F (a:as)) y@(F (b:bs)) | odd_ x && odd_ y = f (cmp a b) where
  f EQ = leftshiftBy (s a) (sub (F as) (F bs))
  f GT = leftshiftBy (s b)
    (sub (leftshiftBy' (sub a b) (F as)) (F bs))
  f LT = leftshiftBy (s a)
    (sub (F as) (leftshiftBy' (sub b a) (F bs)))

sub x@(F (a:as)) y@(F (b:bs)) | odd_ x && even_ y = f (cmp a b) where
  f EQ = leftshiftBy' (s a) (sub (F as) (F bs))
  f GT = leftshiftBy' (s b)
    (sub (leftshiftBy' (sub a b) (F as)) (F bs))
  f LT = leftshiftBy' (s a)
    (sub (F as) (leftshiftBy (sub b a) (F bs)))

sub x@(F (a:as)) y@(F (b:bs)) | even_ x && odd_ y = f (cmp a b) where
  f EQ = s (leftshiftBy (s a) (sub1 (F as) (F bs)))
  f GT =
    s (leftshiftBy (s b)
      (sub1 (leftshiftBy (sub a b) (F as)) (F bs)))
  f LT =
    s (leftshiftBy (s a)
      (sub1 (F as) (leftshiftBy' (sub b a) (F bs))))

sub1 x y = s' (sub x y)

cmp :: T -> T -> Ordering
cmp (F []) (F []) = EQ
cmp (F []) _ = LT
cmp _ (F []) = GT
cmp (F [F []]) (F [F [],F []]) = LT
cmp  (F [F [],F []]) (F [F []]) = GT
cmp x y | x' /= y'  = cmp x' y' where
  x' = bitsize x
  y' = bitsize y
cmp (F xs) (F ys) =
  compBigFirst True True (F (reverse xs)) (F (reverse ys))

compBigFirst :: Bool -> Bool -> T -> T -> Ordering
compBigFirst _ _ (F []) (F []) = EQ
compBigFirst False False (F (a:as)) (F (b:bs)) = f (cmp a b) where
    f EQ = compBigFirst True True (F as) (F bs)
    f LT = GT
    f GT = LT
compBigFirst True True (F (a:as)) (F (b:bs)) = f (cmp a b) where
    f EQ = compBigFirst False False (F as) (F bs)
    f LT = LT
    f GT = GT
compBigFirst False True x y = LT
compBigFirst True False x y = GT

bitsize :: T -> T
bitsize (F []) = (F [])
bitsize (F (x:xs)) = s (foldr add1 x xs)

add1 x y = s (add x y)

ilog2 :: T -> T
ilog2 = s' . bitsize

ilog2star :: T -> T
ilog2star (F []) = F []
ilog2star x = s (ilog2star (ilog2 x))

mul :: T -> T -> T
mul x y = f (cmp x y) where
  f GT = mul1 y x
  f _ = mul1 x y

  mul1 (F []) _ = F []
  mul1 a@(F (x:xs)) y | even_ a =  leftshiftBy (s x) (mul1 (F xs) y)
  mul1 a y | odd_ a = add y (mul1 (s' a) y)

square :: T -> T
square x = mul x x

pow :: T -> T -> T
pow _ (F []) = F [F []]
pow a@(F (x:xs)) b | even_ a = F (s' (mul (s x) b):ys) where
  F ys = pow (F xs) b
pow a b@(F (y:ys)) | even_ b = pow (superSquare y a) (F ys) where
  superSquare (F []) x = square x
  superSquare k x = square (superSquare (s' k) x)
pow x y = mul x (pow x (s' y))

rightshiftBy :: T -> T -> T
rightshiftBy (F [])  y = y
rightshiftBy _ (F []) = F []
rightshiftBy x (F (a:xs)) = f (cmp x a')  where
  b = F xs
  a' = s a
  f LT = F (sub a x:xs)
  f EQ = b
  f GT = rightshiftBy (sub  x a') b

div_and_rem :: T -> T -> (T, T)
div_and_rem x y | LT == cmp x y = (F [],x)
div_and_rem x y | y /= F [] = (q,r) where
  (qt,rm) = divstep x y
  (z,r) = div_and_rem rm y
  q = add (exp2 qt) z

  divstep n m = (q, sub n p) where
    q = try_to_double n m (F [])
    p = leftshiftBy q m

  try_to_double x y k =
    if (LT==cmp x y) then s' k
    else try_to_double x (db y) (s k)

divide :: T -> T -> T
divide n m = fst (div_and_rem n m)

remainder :: T -> T -> T
remainder n m = snd (div_and_rem n m)

isqrt :: T -> T
isqrt (F []) = F []
isqrt n = if cmp (square k) n==GT then s' k else k where
  two = F [F [],F []]
  k=iter n
  iter x = if cmp (absdif r x)  two == LT
    then r
    else iter r where r = step x
  step x = divide (add x (divide n x)) two
absdif x y = if LT == cmp x y then sub y x else sub x y

modPow :: T -> T -> T -> T
modPow m base expo = modStep expo (F [F []]) base where
  modStep(F [F []]) r b  = (mul r b) `remainder` m
  modStep x r b | odd_ x =
    modStep (hf (s' x)) (remainder (mul r b) m)
                        (remainder (square b)  m)
  modStep x r b = modStep (hf x) r (remainder (square b) m)

ll_iter :: T -> T -> T -> T
ll_iter (F []) n m = n
ll_iter k n m = fastmod y m where
   x = ll_iter (s' k) n m
   y = s' (s' (square x))

fastmod :: T -> T -> T
fastmod k m | k == s' m = F []
fastmod k m | LT == cmp k m = k
fastmod k m = fastmod (add q r) m where
  (q,r) = div_and_rem k m

lucas_lehmer :: T -> Bool
lucas_lehmer p | p == s (s (F [])) = True
lucas_lehmer p = F [] ==  (ll_iter p_2 four m) where
  p_2 = s' (s' p)
  four = F [F [F []],F []]
  m  = exp2 p

dyadicSplit :: T -> (T, T)
dyadicSplit z | odd_ z = (F [],z)
dyadicSplit z | even_ z = (s x, s (g xs)) where
  F (x:xs) = s' z

  g [] =  F []
  g (y:ys) = F (y:ys)

randomNats :: Int -> Int -> T -> T -> [T]
randomNats seed k smallest largest = map t ns  where
  ns :: [N]
  ns = take k (randomRs
    (n smallest,n largest) (mkStdGen seed))

oddPrime :: Int -> T -> Bool
oddPrime k m = all strongLiar as where
  m' = s' m
  as = randomNats k k (F [F [],F []]) m'
  (l,d) = dyadicSplit m'

  strongLiar a = (x == F [F []] || (any (== m')
        (squaringSteps l x))) where
    x = modPow m a d

    squaringSteps (F []) _ = []
    squaringSteps l x = x:squaringSteps (s' l)
      (remainder (square x) m)

isProbablyPrime :: T -> Bool
isProbablyPrime (F [F [],F []])  = True
isProbablyPrime x | even_ x = False
isProbablyPrime p = oddPrime 42 p

bitwise :: (Bool -> Bool -> Bool) -> T -> T -> T
bitwise bf (F []) (F []) = F []
bitwise bf (F []) y = if bf False True then y else F []
bitwise bf x (F []) = if bf True False then x else F []

bitwise bf x@(F (a:as)) y@(F (b:bs))  = f (cmp a b) where
  px = odd_ x
  py = odd_ y
  pz = bf px py

  f EQ = fApply bf pz (s a) (F as) (F bs)
  f GT = fApply bf pz (s b) (fromB px (sub a b) (F as)) (F bs)
  f LT = fApply bf pz (s a) (F as) (fromB py (sub b a) (F bs))

  fromB False = leftshiftBy
  fromB True  = leftshiftBy'

  fApply bf False k u v =  leftshiftBy k (bitwise bf u v)
  fApply bf True k u v =  leftshiftBy' k (bitwise bf u v)

bitwiseOr :: T -> T -> T
bitwiseOr = bitwise (||)

bitwiseXor :: T -> T -> T
bitwiseXor = bitwise (/=)

bitwiseAnd :: T -> T -> T
bitwiseAnd = bitwise (&&)

bitwiseNot :: T -> T -> T
bitwiseNot k x = sub y x where y = s' (exp2 k)

bitwiseAndNot :: T -> T -> T
bitwiseAndNot x y = bitwiseNot l d  where
  l = max2 (bitsOf x) (bitsOf y)
  d = bitwiseOr (bitwiseNot l x) y

max2 :: T -> T -> T
max2 x y = if LT==cmp x y then y else x

bitsOf :: T -> T
bitsOf (F []) = s (F [])
bitsOf x = bitsize x

var :: T -> T -> T
var n k = repeatBlocks nbBlocks blockSize mask where
  k' = s k
  nbBlocks = exp2 k'
  blockSize = exp2 (sub n k')
  mask = s' (exp2 blockSize)

  repeatBlocks (F []) _ _ = F []
  repeatBlocks k l mask =
   if odd_ k then r else add mask r where
    r = leftshiftBy l (repeatBlocks (s' k) l mask)

cnf :: T
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

tsize :: T -> T
tsize (F xs) = foldr add1 (F []) (map tsize xs)

iterated :: (T -> T) -> T -> T -> T
iterated f (F []) x = x
iterated f k x = f (iterated f (s' k) x)

bestCase :: T -> T
bestCase k = iterated wTree k (F []) where wTree x = F [x]

worstCase :: T -> T
worstCase k = iterated f k (F []) where f (F xs) = F (F []:xs)

toBinView :: T -> (T, T)
toBinView (F (x:xs)) = (x,F xs)

fromBinView :: (T, T) -> T
fromBinView (x,F xs) = F (x:xs)

dual :: T -> T
dual (F []) = F []
dual x = fromBinView (dual b, dual a) where (a,b) = toBinView x

hd :: T -> T
hd = fst . decons

tl :: T -> T
tl = snd . decons

decons :: T -> (T, T)
decons a@(F (x:xs)) | even_ a = (s x,hf (s' (F xs)))
decons a = (F [],hf (s' a))

cons :: (T, T) -> T
cons (x,y) = leftshiftBy x (s (db y))

syracuse :: T -> T
syracuse n = tl (add n (db (s n)))

nsyr :: T -> [T]
nsyr (F []) = [F []]
nsyr n = n : nsyr (syracuse n)

-- latex formula

l :: T->String
l (F []) = "0"
l (a@(F (x:xs))) | even_ a = "{(2^"++(l1 x)++(l (F xs))++")}"
l (F [x]) = "{(2^{"++(l1 x)++"}-1)}"
l (F (x:xs)) ="{(2^"++(l1 x)++(l1 (F xs))++"-1)}"

l1 :: T -> String
l1 x = "{"++(l x)++"+1}"

-- balanced parentheses representation

cat (F []) = "()"
cat (F xs) = "(" ++ (concatMap cat xs) ++ ")"

toCat m = mapM_ print (map (cat.t) [0..2^m-1])

avgBlockSize (F xs) = sm/len where
  len = fromIntegral (length xs)
  sm = fromIntegral (sum (map (n.s) xs))

avgBlockSizes m = (sum ls) / (fromIntegral max) where
  max = 2^m
  ts = map t [1..max]
  ls = map avgBlockSize ts


-- experiments

collatz (F []) = F []
collatz x| odd_ x = add x (s (db x))
collatz x| even_ x = hf x

ncollatz (F []) = [F []]
ncollatz x = x : ncollatz (collatz x)

op1 f x = n (f (t x))
op2 f x y = n (f (t x) (t y))
op3 f x y z = n (f (t x) (t y) (t z))


