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
  one :: n
  one = arrow empty empty

  s:: n->n
   
  s x | isEmpty x = one
  s x | isEmpty (from x) = adjustWith s (s (to x)) 
  s x = arrow empty (adjustWith p x)
      
  p :: n->n
   
  p x | isEmpty (from x) && isEmpty (to x) = empty
  p x | isEmpty (from x) = adjustWith s (to x)
  p x = arrow empty (p (adjustWith p x))
  
  adjustWith :: (n->n)->n->n
  adjustWith f x = arrow (f (from x)) (to x)

  recursor :: (n -> n -> n) -> n -> n -> n

  recursor f x y | isEmpty x = y
  recursor f x y = f (p x) (recursor f (p x) y)

  itr :: (n -> n) -> n -> n -> n
  itr f t u = recursor g t u where
    g _ y = f y

  recAdd,recMul,recPow :: n -> n -> n

  recAdd = itr s

  recMul x y = itr f y empty where f y = recAdd x y

  recPow x y = itr f y one where f y = recMul x y

  allFrom :: n->[n]
  allFrom k = k : allFrom (s k)
  
  allOf :: [n]
  allOf = allFrom empty

instance PeanoArith T 
instance PeanoArith N

class PeanoArith n=>FastArith n where
 
  isOdd :: n->Bool
  isOdd x = isArrow x && isEmpty (from x)
  
  isEven :: n->Bool
  isEven x = isArrow x && isArrow (from x)

  makeOdd :: n->n
  makeOdd x = arrow empty x
  
  makeEven :: n->n
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

  half,double :: n->n
  
  double = p . makeOdd
  half = trim . s
  
  multiply :: n->n->n
  multiply x _ |isEmpty x = empty
  multiply _ x |isEmpty x = empty   
  multiply x y = arrow 
    (add (from x) (from y)) (add a m) where
       (tx,ty)=(to x,to y)
       a=add tx ty
       m=double (multiply tx ty)

  exp2 :: n->n
  exp2 x = arrow x empty

  pow :: n->n->n -- power y of x
  
  pow _ y | isEmpty y = one
  pow x y | isOdd y = 
    multiply x (pow (multiply x x) (trim y))
  pow x y | isEven y = 
    multiply x' (pow x' (trim y)) where 
      x'=multiply x x

instance FastArith T 
instance FastArith N

class FastArith n=>Ordered n where
  lcmp :: n->n->Ordering
  
  lcmp x y | isEmpty x && isEmpty y = EQ 
  lcmp x y | isEmpty x && not(isEmpty y) = LT
  lcmp x y | not(isEmpty x) && isEmpty y = GT
  lcmp x y = lcmp (trim x) (trim y)

  cmp :: n->n->Ordering
   
  cmp x y = ecmp (lcmp x y) x y where
     ecmp EQ x y = samelen_cmp x y
     ecmp b _ _ = b
     
  samelen_cmp :: n->n->Ordering

  samelen_cmp x y | isEmpty x && isEmpty y = EQ
  samelen_cmp x y | isEmpty x && not(isEmpty y) = LT
  samelen_cmp x y | not(isEmpty x) && isEmpty y = GT
  samelen_cmp x y | isOdd x && isOdd y = 
    samelen_cmp (trim x) (trim y)
  samelen_cmp x y | isEven x && isEven y = 
    samelen_cmp (trim x) (trim y)
  samelen_cmp x y | isOdd x && isEven y = 
    downeq (samelen_cmp (trim x) 
      (trim y)) where
        downeq EQ = LT
        downeq b = b
  samelen_cmp x y | isEven x && isOdd y = 
    upeq (samelen_cmp (trim x) 
      (trim y)) where
        upeq EQ = GT
        upeq b = b

  lt :: n->n->Bool
  lt x y = LT==cmp x y
  
  gt :: n->n->Bool
  gt x y = GT==cmp x y

  nsort :: [n]->[n]
  nsort ns = sortBy cmp ns

instance Ordered T 
instance Ordered N

class Ordered n=>BitVects n where    
  boolAnd :: n->n->n 
  boolAnd x _ | isEmpty x=x
  boolAnd _ y | isEmpty y=y
  boolAnd x y | isOdd x && isOdd y = 
    makeOdd (boolAnd (half x) (half y))
  boolAnd x y = double (boolAnd (half x) (half y))
  
  boolXor :: n->n->n 
  boolXor x y | isEmpty x=y
  boolXor x y | isEmpty y=x
  boolXor x y | (isOdd x && isOdd y) || 
    (isEven x && isEven y) = 
       double (boolXor (half x) (half y))
  boolXor x y = makeOdd (boolXor (half x) (half y))
  
  boolOr :: n->n->n 
  boolOr x y | isEmpty x=y
  boolOr x y | isEmpty y=x
  boolOr x y | isOdd x || isOdd y = 
    makeOdd (boolOr (half x) (half y))
  boolOr x y = double (boolOr (half x) (half y))

  impl :: n->n->n->n
  impl mask a b = boolXor c d where
    d = boolXor mask a
    c = boolAnd a b

  inflate,deflate,inflate',deflate',firstBit :: n->n
  
  inflate x | isEmpty x = empty
  inflate n = boolXor 
     ((double . double . inflate . half) n) (firstBit n)

  deflate x | isEmpty x = empty
  deflate n = boolXor 
    ((double . deflate . half . half) n) (firstBit n)

  deflate' = half . deflate . double
  inflate' = double . inflate

  firstBit n = if isOdd n then one else empty

  bitpair ::  (n,n)->n
  bitpair (x,y) = boolXor (inflate x) (inflate' y)
  
  bitunpair :: n->(n,n)
  bitunpair z = (deflate z, deflate' z)

  vn :: n->n->n
  vn n q | (eq one n) && (eq one q) = one
  vn n q | eq q n = bitpair (vn n one,empty)
  vn n q  | lt q n = bitpair (q',q') where
    q' = vn (p n) q

  boolITE :: n->n->n->n
  boolITE x t e = 
    ((t `boolXor` e) `boolAnd` x) `boolXor` e

  eval_with :: [n]->n->n
  eval_with vs tt | lt tt (exp2 (exp2 n)) = 
    evalToDepth n (map (vn n) vs) tt where
      n = len vs
      
      len [] = empty
      len (_:xs) = s (len (xs))
   
      mask = vn (s n) one
    
      evalToDepth k _ x | isEmpty k && isEmpty x = empty 
      evalToDepth k _ x | isEmpty k = mask
      evalToDepth k (v:vs) x = 
        boolITE v (evalToDepth k' vs l) 
                  (evalToDepth k' vs r) where
          k' = p k
          (l,r) = bitunpair x

  id_eval :: n->n->n
  id_eval n tt = eval_with (vs n) tt where
    vs x | isEmpty x= []
    vs x = x : vs (p x)

  as_prop :: n->n->n
  as_prop n tt = eval_prop tt where
    mask = vn (s n) one
    eval_prop tt | isEmpty tt = empty
    eval_prop tt | lt n tt = 
      impl mask (eval_prop (from tt)) 
                (eval_prop  (to tt))
    eval_prop tt = vn n tt

  v1,v2,v3,axiom1,axiom2 :: n
  
  v1 = one
  v2 = s v1
  v3 = s v2
  axiom1 = arrow v1 (arrow v2 v1)
  axiom2 = arrow (arrow v1 (arrow v2 v3)) 
                 (arrow (arrow v1 v2) (arrow v1 v3))

  show_prop :: N->n->String
  show_prop _ tt | isEmpty tt = "0"
  show_prop x tt | not (lt (view x) tt) = "v"++(show (n tt))
  show_prop x tt = 
      "("++(show_prop x (from tt)) ++ "=>" ++ 
      (show_prop x (to tt))++")"

instance BitVects T 
instance BitVects N

class BitVects n => TypeOperations n where
  typeLowerBound :: n->n->n 
  typeLowerBound x _ |isEmpty x = x
  typeLowerBound _ y |isEmpty y = y
  typeLowerBound x y = arrow 
    (typeLowerBound (from x) (from y))
    (typeLowerBound (to x) (to y))
  
  typeUpperBound :: n->n->n 
  typeUpperBound x y |isEmpty x = y
  typeUpperBound x y |isEmpty y = x
  typeUpperBound x y = arrow 
    (typeUpperBound (from x) (from y))
    (typeUpperBound (to x) (to y))
      
  typeInclusion :: n->n->Bool 
  typeInclusion x y = eq x (typeLowerBound x y)

  deconsWith :: n->n->[n]
  deconsWith t x | typeInclusion t x = dw t x where 
    dw x y |isEmpty x && isEmpty y = [x]
    dw x y |isEmpty x = [y]
    dw x y = dw (from x) (from y) ++ dw (to x) (to y)
  deconsWith _ _ = []
  
  consWith :: n->[n]->n
  consWith t xs = r where 
    (r,[])=tc t xs

    tc t [] = error 
      ("tc error: second arg hits [] at: "++(show t))
    tc t (x:xs) |isEmpty t = (x,xs)
    tc t xs = ((arrow x y),zs)  where
      (x,ys) = tc (from t) xs 
      (y,zs) = tc (to t) ys

  typeExt :: n->n->n 
  typeExt x y |isEmpty x = y
  typeExt x y = arrow (typeExt (from x) y) 
                      (typeExt (to x) y)

instance TypeOperations T 
instance TypeOperations N

class TypeOperations n => Collections n where
  to_list,to_mset,to_set :: n->[n]
  from_list,from_mset,from_set :: [n]->n
  list2mset, mset2list, list2set, set2list :: [n]->[n]
  
  to_list x | isEmpty x = []
  to_list x = (from x) : (to_list (to x))

  from_list [] = empty
  from_list (x:xs) = arrow x (from_list xs)

  list2mset ns = tail (scanl add empty ns)
  mset2list ms =  zipWith sub ms (empty:ms)
    
  list2set = (map p) . list2mset . (map s)
  set2list = (map p) . mset2list . (map s) 
  
  to_mset = list2mset . to_list
  from_mset = from_list . mset2list
  
  to_set = list2set . to_list
  from_set = from_list . set2list

instance Collections T 
instance Collections N

class Collections n => Combinators n where
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
        y = to (from t)
        z = to t
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
instance BitVects Pars
instance TypeOperations Pars
instance Collections Pars
instance Combinators Pars
instance LambdaTerms Pars

