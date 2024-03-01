module Unified where
import Data.List
import Data.Bits

data BitStack = Empty|Bit0 BitStack|Bit1 BitStack 
  deriving (Eq, Show, Read)

empty = Empty

pushBit0 xs = Bit0 xs  
pushBit1 xs = Bit1 xs

popBit (Bit0 xs)=xs
popBit (Bit1 xs)=xs

empty_ x=Empty==x
bit0_ (Bit0 _)=True
bit0_ _ =False

bit1_ (Bit1 _)=True
bit1_ _=False

zero = empty
one = Bit0 empty  
  
peanoSucc xs | empty_ xs = one
peanoSucc xs | bit0_ xs = pushBit1 (popBit xs)
peanoSucc xs | bit1_ xs = pushBit0 (peanoSucc (popBit xs)) 

class (Eq n,Read n,Show n)=>Polymath n where  
  e :: n 
  o_ :: n->Bool
  o :: n->n 
  i :: n->n
  r :: n->n

  e_ :: n->Bool
  e_ x = x==e

  i_ :: n->Bool
  i_ x = not (o_ x || e_ x)

  u :: n
  u = o e
  
  u_ :: n->Bool
  u_ x = o_ x && e_ (r x)

  s :: n->n
  s x | e_ x = u
  s x | o_ x = i (r x)
  s x | i_ x = o (s (r x)) 
  
  p :: n->n
  p x | u_ x = e
  p x | o_ x = i (p (r x)) 
  p x | i_ x = o (r x)

view :: (Polymath a,Polymath b)=>a->b
view x | e_ x = e
view x | o_ x = o (view (r x))
view x | i_ x = i (view (r x))

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

instance Polymath BitStack where
  e=empty
  o=pushBit0
  o_=bit0_ 
  i=pushBit1
  r=popBit

data S=S [S] deriving (Eq,Read,Show)

instance Polymath S where
  e = S []
  
  o_ (S (S []:_)) = True
  o_ _ = False
  
  o (S xs) = s (S (map s xs))
  
  i = s . o

  r (S xs) = S (map p (f ys)) where 
    S ys = p (S xs)
    f (x:xs) | e_ x = xs
    f xs = xs
   
  s (S xs) = S (hLift (S []) xs) where
    hLift k [] = [k]
    hLift k (x:xs) | k==x = hLift (s x) xs
    hLift k xs = k:xs

  p (S xs) = S (hUnLift xs) where
    hUnLift ((S []):xs) = xs
    hUnLift (k:xs) = hUnLift (k':k':xs) where k'= p k 

class (Polymath n) => PolyOrd n where
  polyAdd :: n->n->n 
  polyAdd x y | e_ x = y
  polyAdd x y | e_ y = x
  polyAdd x y | o_ x && o_ y =    i (polyAdd (r x) (r y))
  polyAdd x y | o_ x && i_ y = o (s (polyAdd (r x) (r y)))
  polyAdd x y | i_ x && o_ y = o (s (polyAdd (r x) (r y)))
  polyAdd x y | i_ x && i_ y = i (s (polyAdd (r x) (r y)))
  
  polySubtract :: n->n->n
  polySubtract x y | e_ x && e_ y = e
  polySubtract x y | not(e_ x) && e_ y = x
  polySubtract x y | not (e_ x) && x==y = e
  polySubtract z x | i_ z && o_ x = o (polySubtract (r z) (r x))  
  polySubtract z x | o_ z && o_ x = i (polySubtract (r z) (s (r x)))  
  polySubtract z x | o_ z && i_ x = o (polySubtract (r z) (s (r x)))
  polySubtract z x | i_ z && i_ x = i (polySubtract (r z) (s (r x)))  

  lcmp :: n->n->Ordering
  
  lcmp x y | e_ x && e_ y = EQ 
  lcmp x y | e_ x && not(e_ y) = LT
  lcmp x y | not(e_ x) && e_ y = GT
  lcmp x y = lcmp (r x) (r y)

  cmp :: n->n->Ordering
  cmp x y = ecmp (lcmp x y) x y where
     ecmp EQ x y = samelen_cmp x y
     ecmp b _ _ = b
     
  samelen_cmp :: n->n->Ordering

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

  lt :: n->n->Bool
  lt x y = LT==cmp x y
  
  gt :: n->n->Bool
  gt x y = GT==cmp x y
  
  eq:: n->n->Bool
  eq x y = EQ==cmp x y

  polySort :: [n]->[n]
  polySort ns = sortBy polyCompare ns
  
  polyCompare :: n->n->Ordering
  polyCompare x y | x==y = EQ
  polyCompare x y | lt x y = LT
  polyCompare _ _ = GT

instance PolyOrd Peano
instance PolyOrd BitStack
instance PolyOrd S


class (PolyOrd n) => PolyCalc n where
  polyMultiply :: n->n->n
  polyMultiply x _ | e_ x = e
  polyMultiply _ y | e_ y = e
  polyMultiply x y = s (multiplyHelper (p x) (p y)) where
    multiplyHelper x y | e_ x = y
    multiplyHelper x y | o_ x = o (multiplyHelper (r x) y)
    multiplyHelper x y | i_ x = s (polyAdd y  (o (multiplyHelper (r x) y)))
  
  double :: n->n
  double = p . o
  
  half :: n->n
  half = r . s

  exp2 :: n->n -- power of 2
  exp2 x | e_ x = u
  exp2 x = double (exp2 (p x)) 
  
  pow :: n->n->n -- power y of x
  pow _ y | e_ y = u
  pow x y | o_ y = polyMultiply x (pow (polyMultiply x x) (r y))
  pow x y | i_ y = polyMultiply 
    (polyMultiply x x) 
    (pow (polyMultiply x x) (r y)) 

instance PolyCalc Peano
instance PolyCalc BitStack
instance PolyCalc S

class (PolyCalc n) => PolySet n where
  as_set_nat :: n->[n]
  as_set_nat n = nat2exps n e where
    nat2exps n _ | e_ n = []
    nat2exps n x = if (i_ n) then xs else (x:xs) where
      xs=nat2exps (half n) (s x)

  as_nat_set :: [n]->n
  as_nat_set ns = foldr polyAdd e (map exp2 ns)

  setOp1 :: ([n]->[n])->(n->n)
  setOp1 f = as_nat_set . f . as_set_nat 
  setOp2 :: ([n]->[n]->[n])->(n->n->n)
  setOp2 op x y = as_nat_set (op (as_set_nat x) (as_set_nat y))

  setIntersection :: n->n->n
  setIntersection = setOp2 intersect
                   
  setUnion :: n->n->n
  setUnion = setOp2 union
  
  setDifference :: n->n->n
  setDifference = setOp2 (\\)
  
  setIncl :: n->n->Bool
  setIncl x y = x==setIntersection x y

  powset :: n->n
  powset x = as_nat_set 
    (map as_nat_set (subsets (as_set_nat x))) where
      subsets [] = [[]]
      subsets (x:xs) = [zs|ys<-subsets xs,zs<-[ys,(x:ys)]]   

  inSet :: n->n->Bool
  inSet x y = setIncl (as_nat_set [x]) y 
  
  augmentSet :: n->n
  augmentSet x = setUnion x (as_nat_set [x])

  nthOrdinal :: n->n
  nthOrdinal x | e_ x = e
  nthOrdinal n = augmentSet (nthOrdinal (p n)) 

instance PolySet Peano
instance PolySet BitStack
instance PolySet S

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
  
instance PolyOrd Integer where
  polySubtract x y = abs (x-y)
  lt = (<)
  polyCompare=compare

instance PolyCalc Integer where
  polyMultiply = (*)
  half x = shiftR x 1
  double x = shiftL x 1

instance PolySet Integer where
  setUnion = (.|.)
  setIntersection = (.&.)
  setDifference x y = x .&. (complement y)
  
  inSet x xs = testBit xs (fromIntegral x)
 
  powset 0 = 1
  powset x = xorL (powset (pred x)) where
    xorL n = n `xor` (shiftL n 1)

