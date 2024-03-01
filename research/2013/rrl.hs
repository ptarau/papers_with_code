module RRL where
-- import Visuals

data T = F [T] deriving (Eq,Show,Read)

oddLen [] = False
oddLen [_]= True
oddLen (_:xs) = not (oddLen xs)

odd_ (F []) = False
odd_ (F (_:xs)) = not (oddLen xs) 

even_ (F []) = False
even_ (F (_:xs)) = oddLen xs

n (F []) = 0
n a@(F (x:xs)) | even_ a = 2^(n x + 1)*(n (F xs))
n a@(F (x:xs)) | odd_ a = 2^(n x + 1)*(n (F xs)+1)-1

t 0 = F []
t k | k>0 = F zs where
  (x,y) = if even k then split0 k else split1 k
  F ys = t y
  zs = if x==0 then ys else t (x-1) : ys

split0 z | z> 0 && even z = (1+x,y) where  
  (x,y) = split0  (z `div` 2)
split0 z = (0,z)

split1 z | z>0 && odd z = (1+x,y) where  
  (x,y) = split1  ((z-1) `div` 2)
split1 z = (0,z)

s (F []) = F [F []] -- 1
s (F [x]) = F [x,F []] -- 2

s a@(F (F []:x:xs)) | even_ a = F (s x:xs) -- 3
s a@(F (x:xs)) | even_ a = F (F []:s' x:xs) -- 4

s a@(F (x:F []:y:xs)) | odd_ a = F (x:s y:xs) -- 5
s a@(F (x:y:xs)) | odd_ a = F (x:F []:(s' y):xs) -- 6

s' (F [F []]) = F [] -- 1
s' (F [x,F []]) = F [x] -- 2

s' b@(F (x:F []:y:xs)) | even_ b = F (x:s y:xs) -- 6
s' b@(F (x:y:xs)) |even_ b = F (x:F []:s' y:xs) -- 5

s' b@(F (F []:x:xs)) | odd_ b = F (s x:xs) -- 4
s' b@(F (x:xs)) | odd_ b = F (F []:s' x:xs) -- 3

db (F []) = F []
db a@(F xs) | odd_ a = F (F []:xs)
db a@(F (x:xs)) | even_ a = F (s x:xs) 

hf (F []) = F []
hf (F (F []:xs)) = F xs
hf (F (x:xs)) = F (s' x:xs)

exp2 (F []) = F [F []]
exp2 x = F [s' x,F []]

leftshiftBy (F []) x = x
leftshiftBy _ (F []) = F []
leftshiftBy x k@(F xs) | odd_ k = F ((s' x):xs) 
leftshiftBy x k@(F (y:xs)) | even_ k = F (add x y:xs) 

leftshiftBy' x k = s' (leftshiftBy x (s k)) 

leftshiftBy'' x k = s' (s' (leftshiftBy x (s (s k))))

add (F []) y = y
add x (F []) = x

add x@(F (a:as)) y@(F (b:bs)) |even_ x && even_ y = 
 f (cmp a b) where
  f EQ =  leftshiftBy (s a) (add (F as) (F bs))
  f GT =  leftshiftBy (s b) 
          (add (leftshiftBy (sub a b) (F as)) (F bs))
  f LT =  leftshiftBy (s a) (add (F as) 
          (leftshiftBy (sub b a) (F bs)))

add x@(F (a:as)) y@(F (b:bs)) |even_ x && odd_ y = 
 f (cmp a b) where
  f EQ =  leftshiftBy' (s a) (add (F as) (F bs))
  f GT =  leftshiftBy' (s b) 
          (add (leftshiftBy (sub a b) (F as)) (F bs))
  f LT =  leftshiftBy' (s a) 
          (add (F as) (leftshiftBy' (sub b a) (F bs)))

add x y |odd_ x && even_ y = add y x

add x@(F (a:as)) y@(F (b:bs)) | odd_ x && odd_ y = 
 f (cmp a b) where
  f EQ =  leftshiftBy'' (s a) (add (F as) (F bs))
  f GT =  leftshiftBy'' (s b) 
          (add (leftshiftBy' (sub a b) (F as)) (F bs))
  f LT =  leftshiftBy'' (s a) 
          (add (F as) (leftshiftBy' (sub b a) (F bs)))

sub x (F []) = x
sub x@(F (a:as)) y@(F (b:bs)) | even_ x && even_ y = 
 f (cmp a b) where
  f EQ = leftshiftBy (s a) (sub (F as) (F bs))
  f GT = leftshiftBy (s b) 
         (sub (leftshiftBy (sub a b) (F as)) (F bs))
  f LT = leftshiftBy (s a) 
         (sub (F as) (leftshiftBy (sub b a) (F bs)))

sub x@(F (a:as)) y@(F (b:bs)) | odd_ x && odd_ y = 
 f (cmp a b) where
  f EQ = leftshiftBy (s a) (sub (F as) (F bs))
  f GT = leftshiftBy (s b) 
         (sub (leftshiftBy' (sub a b) (F as)) (F bs))
  f LT = leftshiftBy (s a) 
         (sub (F as) (leftshiftBy' (sub b a) (F bs)))

sub x@(F (a:as)) y@(F (b:bs)) | odd_ x && even_ y = 
 f (cmp a b) where
  f EQ = leftshiftBy' (s a) (sub (F as) (F bs))
  f GT = leftshiftBy' (s b) 
         (sub (leftshiftBy' (sub a b) (F as)) (F bs))
  f LT = leftshiftBy' (s a) 
         (sub (F as) (leftshiftBy (sub b a) (F bs))) 

sub x@(F (a:as)) y@(F (b:bs)) | even_ x && odd_ y = f (cmp a b) where
  f EQ = s (leftshiftBy (s a) (sub1 (F as) (F bs)))
  f GT = s (leftshiftBy (s b) 
         (sub1 (leftshiftBy (sub a b) (F as)) (F bs)))
  f LT = s (leftshiftBy (s a) 
         (sub1 (F as) (leftshiftBy' (sub b a) (F bs))))
  
sub1 x y = s' (sub x y)  

cmp (F []) (F []) = EQ
cmp (F []) _ = LT
cmp _ (F []) = GT
cmp (F [F []]) (F [F [],F []]) = LT
cmp  (F [F [],F []]) (F [F []]) = GT
cmp x y | x' /= y'  = (cmp x' y') where
  x' = bitsize x
  y' = bitsize y
cmp (F xs) (F ys) = 
  compBigFirst True True 
    (F (reverse xs)) (F (reverse ys))

compBigFirst _ _ (F []) (F []) = EQ
compBigFirst False False (F (a:as)) (F (b:bs)) = 
  f (cmp a b) where
    f EQ = compBigFirst True True (F as) (F bs)
    f LT = GT
    f GT = LT   
compBigFirst True True (F (a:as)) (F (b:bs)) = 
  f (cmp a b) where
    f EQ = compBigFirst False False (F as) (F bs)
    f LT = LT
    f GT = GT
compBigFirst False True x y = LT
compBigFirst True False x y = GT

min2 x y = if LT==cmp x y then x else y
max2 x y = if LT==cmp x y then y else x

bitsize (F []) = (F [])
bitsize (F (x:xs)) = s (foldr add1 x xs)

add1 x y = s (add x y)

ilog2 = s'.bitsize

mul x y = f (cmp x y) where
  f GT = mul1 y x
  f _ = mul1 x y
  
  mul1 (F []) _ = F []
  mul1 a@(F (x:xs)) y | even_ a =  
    leftshiftBy (s x) (mul1 (F xs) y)
  mul1 a y | odd_ a =  
    add y (mul1 (s' a) y)

square x = mul x x

pow _ (F []) = F [F []]
pow a@(F (x:xs)) b | even_ a = 
 F (s' (mul (s x) b):ys) where 
  F ys = pow (F xs) b
pow a b@(F (y:ys)) | even_ b = 
 pow (superSquare y a) (F ys) where
  superSquare (F []) x = square x
  superSquare k x = square (superSquare (s' k) x)
pow x y = mul x (pow x (s' y)) -- ?

tsize (F xs) =foldr add1 (F []) (map tsize xs)

iterated f (F []) x = x
iterated f k x = f (iterated f (s' k) x) 

bestCase k = iterated wTree k (F []) where wTree x = F [x]

worseCase k = iterated (s.db.db) k (F []) 

hd = fst.decons

tl = snd.decons

decons (F []) = undefined
decons a@(F (x:xs)) | even_ a = (s x,hf (s' (F xs)))
decons a = (F [],hf (s' a))

cons (x,y) = leftshiftBy x (s (db y))

syracuse n = tl (add n (db (s n)))


nsyr (F []) = [F []]
nsyr n = n : nsyr (syracuse n)

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
          
divide n m = fst (div_and_rem n m)
remainder n m = snd (div_and_rem n m)

isqrt (F []) = F []
isqrt n = if cmp (square k) n==GT then s' k else k where 
  two = F [F [],F []] 
  k=iter n
  iter x = if cmp (absdif r x)  two == LT
    then r 
    else iter r where r = step x
  step x = divide (add x (divide n x)) two    
  
absdif x y = if LT == cmp x y then sub y x else sub x y  

-- experiments
 
collatz (F []) = F []
collatz x| odd_ x = add x (s (db x))
collatz x| even_ x = hf x

ncollatz (F []) = [F []]
ncollatz x = x : ncollatz (collatz x)

op1 f x = n (f (t x))
op2 f x y = n (f (t x) (t y))
op3 f x y z = n (f (t x) (t y) (t z))

{-
n (F []) = 0
n a@(F (x:xs)) | even_ a = 2^(n x + 1)*(n (F xs))
n (F [x]) = 2^(n x +1)-1
n (F (x:xs)) = 2^(n x + 1)*(n (F xs)+1)-1
-}

-- latex formula

l :: T->String
l (F []) = "0"
l (a@(F (x:xs))) | even_ a = "{(2^"++(l1 x)++(l (F xs))++")}"
l (F [x]) = "{(2^{"++(l1 x)++"}-1)}"
l (F (x:xs)) ="{(2^"++(l1 x)++(l1 (F xs))++"-1)}"

l1 :: T -> String
l1 x = "{"++(l x)++"+1}"

