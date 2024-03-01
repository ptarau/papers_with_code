module SharedAxioms where
import Data.List
import Data.Bits
import CPUTime

data BitStack = Empty|Bit0 BitStack|Bit1 BitStack 
  deriving (Eq, Show, Read)

empty = Empty

push0 xs = Bit0 xs  
push1 xs = Bit1 xs

pop (Bit0 xs)=xs
pop (Bit1 xs)=xs

empty_ x=Empty==x
bit0_ (Bit0 _)=True
bit0_ _ =False

bit1_ (Bit1 _)=True
bit1_ _=False

zero = empty
one = Bit0 empty  
  
peanoSucc xs | empty_ xs = one
peanoSucc xs | bit0_ xs = push1 (pop xs)
peanoSucc xs | bit1_ xs = push0 (peanoSucc (pop xs)) 

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

  s :: n->n -- succ
  s x | e_ x = u
  s x | o_ x = i (r x)
  s x | i_ x = o (s (r x)) 
  
  p :: n->n -- pred 
  p x | u_ x = e
  p x | o_ x = i (p (r x)) 
  p x | i_ x = o (r x)

view :: (Polymath a,Polymath b)=>a->b
view x | e_ x = e
view x | o_ x = o (view (r x))
view x | i_ x = i (view (r x))

views :: (Polymath a,Polymath b)=>[a]->[b]
views = map view

newtype A = A Integer deriving (Eq,Show,Read)

instance Polymath A where
  e = A 0
  o_ (A x) = odd x
  o (A x) = A (2*x+1)
  i (A x) = A (2*x+2)
  r (A x) | x/=0 = A ((x-1) `div` 2)

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
  o=push0
  o_=bit0_ 
  i=push1
  r=pop

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
   
  -- override  
  s (S xs) = S (hLift (S []) xs) where
    hLift k [] = [k]
    hLift k (x:xs) | k==x = hLift (s x) xs
    hLift k xs = k:xs

  -- override  
  p (S xs) = S (hUnLift xs) where
    hUnLift ((S []):xs) = xs
    hUnLift (k:xs) = hUnLift (k':k':xs) where k'= p k 

data F = F [F] deriving (Eq,Read,Show)

instance Polymath F where 
  e= F []
  
  o_ (F (F []:_))=True
  o_ _ = False
  
  o (F xs) = F (e:xs)

  i (F xs) = s (F (e:xs))
  
  r (F (x:xs)) | e_ x = F xs
  r (F (k:xs)) = F (hzeros (p k) ++ (hnext xs)) where
    hzeros x | e_ x = []
    hzeros x = e : (hzeros (p x))
  
    hnext [] = []
    hnext (k:xs) = (s k):xs
  
  -- override, co-recursive with r
  s (F xs) = F (hinc xs) where
    hinc ([]) = [e]
    hinc (x:xs) | e_ x= (s k):ys where (k:ys)=hinc xs 
    hinc (k:xs) = e:(p k):xs

  -- override, co-recursive with r
  p (F xs) = F (hdec xs) where
    hdec [x] | e_ x= []
    hdec (x:k:xs) | e_ x= (s k):xs
    hdec (k:xs) = e:(hdec ((p k):xs))

class (Polymath n) => Polymath1 n where
  a :: n->n->n 
  a x y | e_ x = y
  a x y | e_ y = x
  a x y | o_ x && o_ y = i (a (r x) (r y))
  a x y | o_ x && i_ y = o (s (a (r x) (r y)))
  a x y | i_ x && o_ y = o (s (a (r x) (r y)))
  a x y | i_ x && i_ y = i (s (a (r x) (r y)))

  bitlen :: n->n 
  bitlen x | e_ x = e
  bitlen x = s (bitlen (r x))

  sb :: n->n->n 
  sb x y | e_ x = e
  sb x y | e_ y = x
  sb x y = sb (p x) (p y)
  
  lt :: n->n->Bool
  lt x y | e_ x && e_ y = False
  lt x y | e_ x && not (e_ y) = True
  lt x y | not (e_ x) && e_ y = False
  lt x y = lt (p x) (p y)

  nsort :: [n]->[n]
  nsort ns = sortBy ncompare ns
  
  ncompare :: n->n->Ordering
  ncompare x y | x==y = EQ
  ncompare x y | lt x y = LT
  ncompare _ _ = GT

instance Polymath1 A
instance Polymath1 Peano
instance Polymath1 BitStack
instance Polymath1 S
instance Polymath1 F

class (Polymath1 n) => Polymath2 n where
  as_mset_list :: [n]->[n]  
  as_mset_list ns = tail (scanl a e ns)
  
  as_list_mset :: [n]->[n]
  as_list_mset ms = 
    zipWith sb ms' (e: ms') where ms'=nsort ms

  as_set_list :: [n]->[n]
  as_set_list = (map p) . as_mset_list . (map s)
  
  as_list_set :: [n]->[n]
  as_list_set = (map p) . as_list_mset . (map s)  

instance Polymath2 A
instance Polymath2 Peano
instance Polymath2 BitStack
instance Polymath2 S
instance Polymath2 F

class (Polymath2 n) => Polymath3 n where
  m :: n->n->n  -- multiplication
  m x _ | e_ x = e
  m _ y | e_ y = e
  m x y = s (m0 (p x) (p y)) where
    m0 x y | e_ x = y
    m0 x y | o_ x = o (m0 (r x) y)
    m0 x y | i_ x = s (a y  (o (m0 (r x) y)))
  
  db :: n->n -- double
  db = p . o
  
  hf :: n->n -- half
  hf = r . s
  
  exp2 :: n->n -- power of 2
  
  exp2 x | e_ x = u
  exp2 x = db (exp2 (p x)) 
  
  -- simple (slow) division with reminder
  sd :: n->n->(n,n) 
  sd x y = (q,p r) where 
    (q,r) = sd' (s x) y
    sd' x y | e_ x = (e,e)
    sd' x y = z where 
      x_y=sb x y
      z=if e_ x_y 
        then (e,x) 
        else (s q,r) where (q,r)=sd' x_y y

  to_bin :: n->[n]
  to_bin x | e_ x = []
  to_bin x | o_ x = u: (to_bin (hf x))
  to_bin x = e:  (to_bin (hf x))
  
  from_bin :: [n]->n
  from_bin [] = e
  from_bin (x:xs) | u_ x = o (from_bin xs)
  from_bin (x:xs) | e_ x = db (from_bin xs)

instance Polymath3 A
instance Polymath3 Peano
instance Polymath3 BitStack
instance Polymath3 S
instance Polymath3 F

data Pairing n = 
     Pairing {p2 :: (n->n->n), p0 :: n->n, p1 :: n->n}          

class (Polymath3 n) => Polymath4 n where
  ppairing :: Pairing n  
  ppairing = Pairing {p2=ppair,p0=pfirst,p1=psecond}
  
  ppair :: n->n->n
  ppair x y = p (lcons x y) where
    lcons x ys = s (lcons' x (db ys))  
    lcons' x ys | e_ x = ys
    lcons' x ys = o  (lcons' (p x) ys)
  
  pfirst :: n->n  
  pfirst z = lhead (s z) where
    lhead = h . p 
    h xs | o_ xs = s (h (hf xs))
    h _ = e

  psecond :: n->n
  psecond z = ltail (s z) where
    ltail =  hf . t . p
    t xs | o_ xs = t (hf xs)
    t xs  = xs

  bpairing :: Pairing n  
  bpairing = Pairing {p2=bpair,p0=bfirst,p1=bsecond}
  
  bpair :: n -> n -> n
  bpair x y = from_bin (bpair' (to_bin x) (to_bin y)) where
    bpair' [] [] = []
    bpair' [] ys = e:(bpair' ys [])
    bpair' (x:xs) ys = x:(bpair' ys xs)
  
  bfirst ::  n -> n
  bfirst = from_bin . deflate . to_bin
 
  bsecond :: n -> n
  bsecond = from_bin . second' . to_bin where 
    second' [] = []
    second' (_:xs) = deflate xs

  deflate :: [n]-> [n]
  deflate [] = []
  deflate (x:_:xs) = x:(deflate xs)
  deflate [x] = [x]

instance Polymath4 A
instance Polymath4 Peano
instance Polymath4 BitStack
instance Polymath4 S
instance Polymath4 F

class (Polymath4 n) => Polymath5 n where
  pairing :: Pairing n
  pairing = ppairing -- default pairing - to override
  
  first :: n->n
  first = p0 pairing

  second :: n->n
  second = p1 pairing
  
  pair :: n->n->n
  pair = p2 pairing

  hd ::  n -> n
  hd n = first (p n)
  
  tl :: n -> n
  tl n = second (p n)
  
  cons :: n -> n -> n
  cons x y = s (pair x y)
    
  -- numbers as lists and back
  as_list_nat :: n->[n]
  as_list_nat x | e_ x = []
  as_list_nat x = hd x : as_list_nat (tl x)
 
  as_nat_list :: [n]->n  
  as_nat_list [] = e
  as_nat_list (x:xs) = cons x (as_nat_list xs)

  as_nat_set :: [n]->n
  as_nat_set = as_nat_list . as_list_set
  
  as_set_nat :: n->[n]
  as_set_nat = as_set_list . as_list_nat

  as_nat_mset :: [n]->n
  as_nat_mset = as_nat_list . as_list_mset
  
  as_mset_nat :: n->[n]
  as_mset_nat = as_mset_list . as_list_nat

  ordUnpair :: n->(n,n)
  ordUnpair z = (first z,second z)
  
  ordPair :: (n,n)->n
  ordPair (x,y) = pair x y

  unordUnpair :: n->(n,n)
  unordUnpair z = (x',y') where 
    (x,y)=ordUnpair z
    [x',y']=as_mset_list  [x,y]
  
  unordPair :: (n,n)->n  
  unordPair (x,y) = ordPair (x',y') where 
    [x',y']=as_list_mset [x,y]

  upwardUnpair :: n->(n,n)
  upwardUnpair z = (x',y') where 
    (x,y)=ordUnpair z
    [x',y']=as_set_list [x,y]
  
  upwardPair :: (n,n)->n
  upwardPair (x,y) = ordPair (x',y') where 
    [x',y']=as_list_set [x,y]

instance Polymath5 A
instance Polymath5 Peano
instance Polymath5 BitStack
instance Polymath5 S
instance Polymath5 F

class (Polymath5 n) => Polymath6 n where
  setOp1 :: ([n]->[n])->(n->n)
  setOp1 f = as_nat_set . f . as_set_nat 
  setOp2 :: ([n]->[n]->[n])->(n->n->n)
  setOp2 op x y = as_nat_set 
    (op (as_set_nat x) (as_set_nat y))

  setIntersection :: n->n->n
  setIntersection = setOp2 intersect
                   
  setUnion :: n->n->n
  setUnion = setOp2 union
  
  setDifference :: n->n->n
  setDifference = setOp2 (\\)
  
  setIncl :: n->n->Bool
  setIncl x y = x==(setIntersection x y)

  powset :: n->n
  powset x = as_nat_set 
    (map as_nat_set (subsets (as_set_nat x))) where
      subsets [] = [[]]
      subsets (x:xs) = 
         [zs|ys<-subsets xs,zs<-[ys,(x:ys)]]   

  inSet :: n->n->Bool
  inSet x y = setIncl (as_nat_set [x]) y 
  
  augment :: n->n
  augment x = setUnion x (as_nat_set [x])

  nthOrdinal :: n->n
  nthOrdinal x | e_ x = e
  nthOrdinal n = augment (nthOrdinal (p n)) 

instance Polymath6 A
instance Polymath6 Peano
instance Polymath6 BitStack
instance Polymath6 S
instance Polymath6 F

class (Polymath6 n) => Polymath7 n where
  listOp1 :: ([n]->[n])->(n->n)
  listOp1 f = as_nat_list . f . as_list_nat 
  listOp2 :: ([n]->[n]->[n])->(n->n->n)
  listOp2 op x y = as_nat_list 
    (op (as_list_nat x) (as_list_nat y))

  listConcat :: n->n->n
  listConcat = listOp2 (++)
                   
  listReverse :: n->n
  listReverse = listOp1 reverse

  listFoldr :: (n -> n -> n) -> n -> n -> n
 
  listFoldr f z xs | e_ xs    =  z
  listFoldr f z xs =  f (hd xs) (listFoldr f z (tl xs))

  listConcat' :: n->n->n
  listConcat' xs ys = listFoldr cons ys xs 
  
  listSum :: n->n
  listSum = listFoldr a u
  
  listProduct :: n->n
  listProduct = listFoldr m u

instance Polymath7 A
instance Polymath7 Peano
instance Polymath7 BitStack
instance Polymath7 S
instance Polymath7 F

newtype B = B Integer deriving (Eq,Show,Read)
 
instance Polymath B where
  e = B 0
  o_ (B x) = odd x
  o (B x) = B (2*x+1)
  i (B x) = B (2*x+2)
  r (B x) | x/=0 = B ((x-1) `div` 2)
  
instance Polymath1 B
instance Polymath2 B
instance Polymath3 B 
instance Polymath4 B 
instance Polymath5 B where pairing=bpairing 
instance Polymath6 B
instance Polymath7 B


instance Polymath Integer where
  e = 0
  o_ x = testBit x 0
 
  o x = succ (shiftL x 1) 
  i  = succ . o
  r x | x/=0 = shiftR (pred x) 1

  s = succ
  p = pred
  u = 1
  u_ = (== 1)
  
instance Polymath1 Integer where
  sb x y = abs (x-y)
  lt = (<)
  nsort = sort
  ncompare=compare

instance Polymath2 Integer
instance Polymath3 Integer where
  m = (*)
  hf x = shiftR x 1
  db x = shiftL x 1
  sd = quotRem
 
instance Polymath4 Integer  
instance Polymath5 Integer

instance Polymath6 Integer where
  setUnion = (.|.)
  setIntersection = (.&.)
  setDifference x y = x .&. (complement y)
  
  inSet x xs = testBit xs (fromIntegral x)
 
  powset 0 = 1
  powset x = y `xor` (shiftL y 1) where y=powset (pred x) 
  
instance Polymath7 Integer

powset' i = product (map (\k->1+2^(2^k)) (as_set_nat i)) 

data Iso a b = Iso (a->b) (b->a)

compose :: Iso a b -> Iso b c -> Iso a c
compose (Iso f g) (Iso f' g') = Iso (f' . f) (g . g')

itself = Iso id id
invert (Iso f g) = Iso g f

type Type a = Iso a Integer

nat :: Type Integer
nat = itself

as :: Type a -> Type b -> b -> a
as that this x = g x where 
   Iso _ g = compose that (invert this)

borrow_from :: Type b -> (b -> b) ->
               Type a -> a -> a

borrow_from lender f borrower = 
  (as borrower lender) . f . (as lender borrower)

borrow_from2 :: Type a -> (a -> a -> a) -> 
                Type b -> b -> b -> b

borrow_from2 lender op borrower x y = 
    as borrower lender r where
       x'= as lender borrower x
       y'= as lender borrower y
       r = op x' y'

list :: Type [Integer]
list = Iso  as_nat_list as_list_nat

set :: Type [Integer]
set = Iso  as_nat_set as_set_nat

mset :: Type [Integer]
mset = Iso  as_nat_mset as_mset_nat

class (Polymath7 n) => Polymath8 n where

  as_set_digraph :: [(n,n)]->[n]
  as_set_digraph = map ordPair
  
  as_digraph_set :: [n]->[(n,n)]
  as_digraph_set = map ordUnpair

  as_set_graph :: [(n,n)]->[n]
  as_set_graph = map unordPair
  
  as_graph_set :: [n]->[(n,n)]
  as_graph_set = map unordUnpair

  as_set_dag :: [(n,n)]->[n]
  as_set_dag  = map upwardPair
  
  as_dag_set :: [n]->[(n,n)]
  as_dag_set = map upwardUnpair

  as_hypergraph_set :: [n]->[[n]]
  as_hypergraph_set = map (as_set_nat . s)
  
  as_set_hypergraph :: [[n]]->[n]
  as_set_hypergraph = map (p . as_nat_set)

instance Polymath8 A
instance Polymath8 Peano
instance Polymath8 BitStack
instance Polymath8 S
instance Polymath8 F
instance Polymath8 B
instance Polymath8 Integer

type N2=(Integer,Integer)

digraph :: Type [N2]
digraph = compose (Iso as_set_digraph as_digraph_set) set

graph :: Type [N2]
graph = compose (Iso as_set_graph as_graph_set) set

dag :: Type [N2]
dag = compose (Iso as_set_dag as_dag_set) set

hypergraph :: Type [[Integer]]
hypergraph = 
  compose (Iso as_set_hypergraph as_hypergraph_set) set

syr n = tl (a (m six n) four) where 
  four = s (s (s (s e)))
  six = s (s four)

nsyr n | e_ n = [e]
nsyr n = n : nsyr (syr n)

cs::[Integer]
cs=[1234567890,12345678901234567890,
    123456789012345678901234567890]

benchmark n = do
  x<-getCPUTime
  print (length (nsyr n))
  y<-getCPUTime
  let t=(y-x) `div` 1000000000
  return ("time="++(show t))

cI c = c :: Integer
cA c=view (c :: Integer) :: A 
cK c=view (c :: Integer) :: BitStack 
cF c=view (c :: Integer) :: F
cS c=view (c :: Integer) :: S

