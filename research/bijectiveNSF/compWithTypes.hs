-- please use "ghci -XTypeSynonymInstances" to run this code
-- tested with GHC 6.12.1
module SystemT where
import Data.List
import Data.Bits
--import Visuals

class (Read n,Show n) => PureTypes n where  
  empty :: n
  isEmpty :: n->Bool
  arrow :: n->n->n
  from,to :: n->n

  isArrow :: n->Bool
  isArrow = not . isEmpty
  
  eq :: n -> n -> Bool
  eq x y | isEmpty x && isEmpty y = True
  eq x y | isEmpty x || isEmpty y = False
  eq x y = eq (from x) (from y) && eq (to x) (to y)

pure_type_prop1 :: (PureTypes n) => n -> Bool
pure_type_prop2 :: (PureTypes n) => n -> n -> Bool

pure_type_prop1 z = isEmpty z || 
  eq z (arrow (from z) (to z))
pure_type_prop2 x y = eq x (from z) && eq y (to z) 
  where z = arrow x y

view :: (PureTypes a,PureTypes b)=>a->b
view x | isEmpty x = empty
view x = arrow (view (from x)) (view (to x))

prop_view :: (PureTypes a,PureTypes b) => a->b->Bool
prop_view x y = iso view view x y where
  iso :: (PureTypes a,PureTypes b) => 
         (a->b)->(b->a)->a->b->Bool
  iso f g x y = eq ((f . g) y) y && eq ((g . f) x) x

infixr 5 :->
data T = E|T :-> T deriving (Read, Show)

instance PureTypes T where
  empty = E

  isEmpty E = True
  isEmpty _ = False

  arrow = (:->)

  from E = undefined
  from (x :-> _) = x

  to E = undefined
  to (_ :-> y) = y
  
t :: (PureTypes a)=>a->T
t = view

type N = Integer

instance PureTypes N where
  empty=0

  isEmpty 0 = True
  isEmpty _ = False

  arrow x y = (2^x)*(2*y+1)

  from x | x>0 = 
    if odd x then 0 else 1+(from  (x `div` 2))
  from _ = undefined

  to x | x>0 = 
    if odd x then (x-1) `div` 2 else to (x `div` 2)
  to _ = undefined

n :: (PureTypes a)=>a->N
n = view

class PureTypes n=>PeanoArith n where 
  s :: n->n
   
  s z | isEmpty z = arrow empty empty
  s z | isEmpty (from z) = arrow (s (from (s (to z))))
    (to (s (to z)))
  s z = arrow empty (arrow (p (from z)) (to z))      

  p :: n->n
   
  p z | isEmpty (from z) && isEmpty (to z) = empty
  p z | isEmpty (from z) = arrow (s (from (to z))) 
    (to (to z))
  p z = arrow empty (p (arrow (p (from z)) (to z)))  

instance PeanoArith T 
instance PeanoArith N

class PeanoArith n=>FastArith n where
  one :: n
  one = arrow empty empty
   
  isOdd,isEven :: n->Bool
  isOdd x = isArrow x && isEmpty (from x)
  isEven x = isArrow x && isArrow (from x)

  makeOdd,makeEven :: n->n
  makeOdd x = arrow empty x
  makeEven = s . makeOdd

  trim :: n->n
 
  trim x | isEmpty (from x) = to x
  trim x = p (arrow (p (from x)) (to x)) 

  add :: n->n->n 
  add x y | isEmpty x = y
  add x y | isEmpty y = x
  add x y | isOdd x && isOdd y = makeEven
     (add (trim x) (trim y))
  add x y | isOdd x && isEven y = makeOdd
     (s (add (trim x) (trim y)))
  add x y | isEven x && isOdd y = makeOdd
     (s (add (trim x) (trim y)))
  add x y | isEven x && isEven y = makeEven
     (s (add (trim x) (trim y)))
  
  sub :: n->n->n
  sub x y | isEmpty x && isEmpty y = empty
  sub x y | not(isEmpty x) && isEmpty y = x
  sub x y | not (isEmpty x) && eq x y = empty
  sub y x | isEven y && isOdd x = makeOdd
     (sub (trim y) (trim x))  
  sub y x | isOdd y && isOdd x = makeEven
     (sub (trim y) (s (trim x)))  
  sub y x | isOdd y && isEven x = makeOdd
     (sub (trim y) (s (trim x)))
  sub y x | isEven y && isEven x = makeEven
     (sub (trim y) (s (trim x)))  

  lsize :: n->n
  lsize x | isEmpty x = one
  lsize x = add (lsize (from x)) (lsize (to x))

  multiply :: n->n->n
  
  multiply x _ |isEmpty x = empty
  multiply _ x |isEmpty x = empty   
  multiply x y = arrow 
    (add (from x) (from y)) (add a m) where
       (tx,ty)=(to x,to y)
       a=add tx ty
       m=double (multiply tx ty)

  half,double :: n->n
  double = p . makeOdd
  half = trim . s
  
  exp2 :: n->n
  exp2 x = arrow x empty

  pow :: n->n->n  
  pow _ y | isEmpty y = one
  pow x y | isOdd y = 
    multiply x (pow (multiply x x) (trim y))
  pow x y | isEven y = 
    multiply x' (pow x' (trim y)) where 
      x'=multiply x x

instance FastArith T 
instance FastArith N

class FastArith n => Ordered n where
  cmp :: n->n->Ordering
 
  cmp x y | isEmpty x && isEmpty y = EQ
  cmp x y | isEmpty x && not(isEmpty y) = LT
  cmp x y | not(isEmpty x) && isEmpty y = GT
  cmp x y | isOdd x && isOdd y = 
    cmp (trim x) (trim y)
  cmp x y | isEven x && isEven y = 
    cmp (trim x) (trim y)
  cmp x y | isOdd x && isEven y = 
    downeq (cmp (trim x) 
      (trim y)) where
        downeq EQ = LT
        downeq b = b
  cmp x y | isEven x && isOdd y = 
    upeq (cmp (trim x) 
      (trim y)) where
        upeq EQ = GT
        upeq b = b

  lt, gt :: n->n->Bool
  
  lt x y = LT==cmp x y
  gt x y = GT==cmp x y

  div_and_rem :: n->n->(n,n)
  
  div_and_rem x y | lt x y = (empty,x)
  div_and_rem x y | gt y empty = (add (exp2 qt) u,v) where 
    exp2leq_then n m = try_to_double n m empty where
      try_to_double x y k | lt x y = p k
      try_to_double x y k = try_to_double x (double y) (s k)     
    divstep n m = (q, sub n n') where
      q = exp2leq_then n m 
      n' = multiply (exp2 q) m    
    (qt,rm) = divstep x y
    (u,v) = div_and_rem rm y
    
  divide,reminder :: n->n->n
  
  divide n m = fst (div_and_rem n m)
  reminder n m = snd (div_and_rem n m)

instance Ordered T 
instance Ordered N

class Ordered n => Combinators n where
  cS,cK :: n
  cS = arrow empty one
  cK = arrow one empty

  isS,isK :: n->Bool
  isS x = isArrow x && isEmpty (from x) && isArrow (to x)
    && isEmpty (from (to x)) && isEmpty (to (to x))
  isK x = isArrow x && isEmpty (to x) && isArrow (from x)
    && isEmpty (from (from x)) && isEmpty (to (from x))

  redSK :: n -> n
  redSK t | isK t = t
  redSK t | isS t = t
  redSK t | isArrow t && isArrow (from t) 
      && isK (from (from t)) = redSK (to (from t))
  redSK t | isArrow t && isArrow (from t) && 
      isArrow (from (from t)) &&
      isS (from (from (from t))) = xzyz where
        x = to (from (from t))
        (y,z) = (to (from t),to t)
        (xz,yz) = (arrow x z,arrow y z)
        xzyz = redSK (arrow xz yz)
  redSK t | isArrow t = t' where
      (x,y) = (from t,to t)
      (x',y') = (redSK x,redSK y)
      (z,z') = (arrow x y,arrow x' y')
      t'= if (eq z z') then z' else redSK z'
  redSK t = t

  cI,cT,cF :: n
  cI = arrow (arrow cS cK) cK
  cT = cK
  cF = arrow cK cI

  test_t,test_f:: n
  test_t = redSK (arrow (arrow cT cK) cS)
  test_f = redSK (arrow (arrow cF cK) cS)

  cX :: n
  cX = empty
  
  isX :: n->Bool
  isX = isEmpty
  
  redX :: n -> n
  redX = redSK

instance Combinators T
instance Combinators N

class Combinators n => LambdaTerms n where
  occursIn :: n -> n -> Bool
  occursIn expr x | isEmpty expr && isEmpty x = True
  occursIn expr x | isEmpty x || isEmpty expr = False
  occursIn expr x | isOdd x = occursIn (from expr) (trim x) 
  occursIn expr x | isEven x = occursIn (to expr) (trim x) 

  applyLambda :: [n] -> n -> n -> Maybe n
  applyLambda xs expr val | all (occursIn expr) xs = 
   Just (foldl (substWith val) expr xs)
  applyLambda _ _ _ = Nothing

  substWith :: n -> n -> n -> n
  substWith val expr x | isEmpty expr = val
  substWith val expr x | isOdd x = arrow l r where
    l =  substWith val (from expr) (trim x)
    r = to expr
  substWith val expr x| isEven x = arrow l r where
    l = from expr
    r = substWith val (to expr) (trim x)

instance LambdaTerms T
instance LambdaTerms N

data Par = L|R deriving (Eq,Read,Show)
data Pars = Pars [Par] deriving (Eq,Read,Show)

instance PureTypes Pars where
  empty=Pars [L,R]
  arrow (Pars x) (Pars (L:xs)) =  Pars (L : x ++ xs)
  from = fst . from_to
  to = snd . from_to
  
  isEmpty (Pars [L,R]) = True
  isEmpty _ = False

from_to (Pars (c:cs)) | c==L = 
  (Pars (L:fs),Pars (L:ts)) where
    (fs,ts)=parexpr cs

parexpr (c:cs) | c==L = parlist cs where 
  parlist (c:cs) | c==R = ([R],cs)
  parlist (c:cs) = (c:fs++ts,cs2) where 
    (fs,cs1)=parexpr (c:cs)
    (ts,cs2)=parlist cs1

par :: (PureTypes a)=>a->Pars
par = view

instance PeanoArith Pars
instance FastArith Pars
instance Ordered Pars
instance Combinators Pars
instance LambdaTerms Pars

