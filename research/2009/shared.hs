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

  view :: (Polymath a)=>a->n
  view x | e_ x = e
  view x | o_ x = o (view (r x))
  view x | i_ x = i (view (r x))

newtype N = N Integer deriving (Eq,Show,Read)

instance Polymath N where
  e = N 0
  o_ (N x) = odd x
  o (N x) = N (2*x+1)
  i (N x) = N (2*x+2)
  r (N x) | x/=0 = N ((x-1) `div` 2)

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
   
  s (S xs) = S (hLift (S []) xs) where
    hLift k [] = [k]
    hLift k (x:xs) | k==x = hLift (s x) xs
    hLift k xs = k:xs

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
  r (F (k:xs)) = F (hpad (p k) (hnext xs)) where
    hpad x xs | e_ x = xs
    hpad x xs = e : (hpad (p x) xs)
  
    hnext [] = []
    hnext (k:xs) = (s k):xs
  
  s (F xs) = F (hinc xs) where
    hinc ([]) = [e]
    hinc (x:xs) | e_ x= (s k):ys where (k:ys)=hinc xs 
    hinc (k:xs) = e:(p k):xs

  p (F xs) = F (hdec xs) where
    hdec [x] | e_ x= []
    hdec (x:k:xs) | e_ x= (s k):xs
    hdec (k:xs) = e:(hdec ((p k):xs))

class (Polymath n) => Polymath1 n where
  a :: n->n->n 
  a x y | e_ x = y
  a x y | e_ y = x
  a x y | o_ x && o_ y =    i (a (r x) (r y))
  a x y | o_ x && i_ y = o (s (a (r x) (r y)))
  a x y | i_ x && o_ y = o (s (a (r x) (r y)))
  a x y | i_ x && i_ y = i (s (a (r x) (r y)))
  
  d :: n->n->n
  d x y | e_ x && e_ y = e
  d x y | not(e_ x) && e_ y = x
  d x y | not (e_ x) && x==y = e
  d z x | i_ z && o_ x = o (d (r z) (r x))  
  d z x | o_ z && o_ x = i (d (r z) (s (r x)))  
  d z x | o_ z && i_ x = o (d (r z) (s (r x)))
  d z x | i_ z && i_ x = i (d (r z) (s (r x)))  

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

  nsort :: [n]->[n]
  nsort ns = sortBy ncompare ns
  
  ncompare :: n->n->Ordering
  ncompare x y | x==y = EQ
  ncompare x y | lt x y = LT
  ncompare _ _ = GT

instance Polymath1 N
instance Polymath1 Peano
instance Polymath1 BitStack
instance Polymath1 S
instance Polymath1 F

class (Polymath1 n) => Polymath2 n where
  as_mset_list :: [n]->[n]  
  as_mset_list ns = tail (scanl a e ns)
  
  as_list_mset :: [n]->[n]
  as_list_mset ms = 
    zipWith d ms' (e: ms') where ms'=nsort ms

  as_set_list :: [n]->[n]
  as_set_list = (map p) . as_mset_list . (map s)
  
  as_list_set :: [n]->[n]
  as_list_set = (map p) . as_list_mset . (map s)  

instance Polymath2 N
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

  pow :: n->n->n -- power y of x
  pow _ y | e_ y = u
  pow x _ | e_ x = e 
  pow x y | o_ y = z where 
    b=x
    b'=pow b (r y)
    z=m b (m b' b')
  pow x y | i_ y = z where 
    b=m x x
    b'=pow b (r y)
    z=m b (m b' b')

instance Polymath3 N
instance Polymath3 Peano
instance Polymath3 BitStack
instance Polymath3 S
instance Polymath3 F

class (Polymath3 n) => Polymath4 n where
  pair :: n->n->n
  pair x y = p (lcons x y) where
    lcons x ys = s (lcons' x (db ys))  
    lcons' x ys | e_ x = ys
    lcons' x ys = o  (lcons' (p x) ys)
  
  first :: n->n  
  first z = lhead (s z) where
    lhead = h . p 
    h xs | o_ xs = s (h (hf xs))
    h _ = e

  second :: n->n
  second z = ltail (s z) where
    ltail =  hf . t . p
    t xs | o_ xs = t (hf xs)
    t xs  = xs

instance Polymath4 N
instance Polymath4 Peano
instance Polymath4 BitStack
instance Polymath4 S
instance Polymath4 F

class (Polymath4 n) => Polymath5 n where
  hd ::  n -> n
  hd = first . p
  
  tl :: n -> n
  tl = second . p
  
  cons :: n -> n -> n
  cons x y = s (pair x y)
  
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

instance Polymath5 N
instance Polymath5 Peano
instance Polymath5 BitStack
instance Polymath5 S
instance Polymath5 F

class (Polymath5 n) => Polymath6 n where
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
  setIncl x y = x==(setIntersection x y)

  powset :: n->n
  powset x = as_nat_set 
    (map as_nat_set (subsets (as_set_nat x))) where
      subsets [] = [[]]
      subsets (x:xs) = [zs|ys<-subsets xs,zs<-[ys,(x:ys)]]   

  inSet :: n->n->Bool
  inSet x y = setIncl (as_nat_set [x]) y 
  
  augment :: n->n
  augment x = setUnion x (as_nat_set [x])

  nthOrdinal :: n->n
  nthOrdinal x | e_ x = e
  nthOrdinal n = augment (nthOrdinal (p n)) 

instance Polymath6 N
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

instance Polymath7 N
instance Polymath7 Peano
instance Polymath7 BitStack
instance Polymath7 S
instance Polymath7 F

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
  
instance Polymath1 Integer where
  d x y = abs (x-y)
  lt = (<)
  nsort = sort
  ncompare=compare

instance Polymath2 Integer
instance Polymath3 Integer where
  m = (*)
  hf x = shiftR x 1
  db x = shiftL x 1
  
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

instance Polymath8 N
instance Polymath8 Peano
instance Polymath8 BitStack
instance Polymath8 S
instance Polymath8 F
instance Polymath8 Integer

syracuse n = tl (a (m six n) four) where 
  four = s (s (s (s e)))
  six = s (s four)

nsyr n | e_ n = [e]
nsyr n = n : nsyr (syracuse n)

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
cN c=view (c :: Integer) :: N 
cK c=view (c :: Integer) :: BitStack 
cF c=view (c :: Integer) :: F
cS c=view (c :: Integer) :: S

