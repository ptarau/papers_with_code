module XDB where
import System.Random
import Math.Combinat.Trees
import GCat

data B a = Vb a | Lb (B a) | Ab (B a) (B a) deriving (Eq,Show,Read)

data X a = Vx a a | Ax a (X a) (X a) deriving (Eq,Show,Read)

isClosedX :: Cat a => X a -> Bool
isClosedX t = f t e where
  f (Vx k n) d = LT==cmp n (add d k)
  f (Ax k x y) d = f x d' && f y d' where d' = add d k

b2x :: (Cat a) => B a -> X a
b2x (Vb x) = Vx e x
b2x (Ab x y) = Ax e (b2x x) (b2x y) 
b2x (Lb x) = f e x where
  f k (Ab x y) = Ax (s k) (b2x x) (b2x y)
  f k (Vb x) = Vx (s k) x
  f k (Lb x) = f (s k) x

x2b :: (Cat a) => X a -> B a
x2b (Vx k x)  = iterLam k (Vb x)
x2b (Ax k x y) = iterLam k (Ab (x2b x) (x2b y))

iterLam :: Cat a => a -> B a -> B a
iterLam k x | e_ k = x
iterLam k x = iterLam (s' k) (Lb x)

isClosedB :: Cat a => B a -> Bool
isClosedB = isClosedX . b2x

x2t :: Cat a => X a -> a
x2t (Vx k n) | e_ k && e_ n = n
x2t (Vx k n) = c (s' (s' (c (n,k))),e)
x2t (Ax k a b) = c (k,q) where q = c (x2t a,x2t b)

t2x :: Cat a => a -> X a
t2x x | e_ x = Vx x x
t2x z = f y where
  (x,y) = c' z
  f y | e_ y = Vx k n where (n,k) = c' (s (s x))
  f y | c_ y = Ax x (t2x a) (t2x b) where (a,b) = c' y

t2b :: Cat a => a -> B a
t2b = x2b . t2x

b2t :: Cat a => B a -> a
b2t = x2t . b2x

sizeT :: Cat t => t -> t
sizeT x | e_ x = x
sizeT x = s (add (sizeT a) (sizeT b)) where (a,b) = c' x

sizeX :: Cat a => X a -> a
sizeX (Vx k n) = add (sizeT k) (sizeT n)
sizeX (Ax k a b) = 
  s (add (sizeT k) (add (sizeX a) (sizeX b)))

data S a = Vs a | Ls a (S a) | As (S a) (S a) 
           deriving (Eq,Show,Read)

b2s :: Cat a => B a -> S a
b2s a = f a e [] where
  f :: (Cat a) => B a -> a -> [a] -> S a
  f (Vb i) _ vs =  Vs (at i vs)
  f (Lb a) v vs = Ls v (f a (s v) (v:vs))
  f (Ab a b) v vs = As (f a v vs) (f b v vs)

at i (x:_) | e_ i = x 
at i (_:xs) = at (s' i) xs   

s2b  :: Cat a => S a -> B a
s2b x = f x [] where
  f :: Cat a => S a -> [a] -> B a
  f (Vs x) vs = Vb  (at x vs)
  f (As x y) vs = Ab (f x vs) (f y vs)    
  f (Ls v y) vs = Lb a where a = f y (v:vs) 

data H a = Vh a | Lh (H a -> H a) | Ah (H a) (H a) 

nf :: H a -> H a
nf (Vh a) = Vh a
nf (Lh f)   = Lh (nf . f)
nf (Ah f a) = h (nf f) (nf a) where
  h :: H a -> H a -> H a
  h (Lh g) x = g x
  h g x = Ah g x

h2b :: Cat a => H a -> B a
h2b t = h e t where
  h d  (Lh f)  = Lb  (h d' (f (Vh d'))) where d' = s d
  h d  (Ah a b) = Ab (h d a) (h d b)
  h d  (Vh d')  = Vb (sub d d')

b2h :: Cat a => B a -> H a
b2h t = h t [] where
  h :: Cat a =>  B a  -> [H a] -> H a
  h (Lb a) xs  = Lh (\x -> h a (x:xs))
  h (Ab a b) xs = Ah (h a xs) (h b xs)
  h (Vb i) xs  = at i xs

evalB :: (Cat a) => B a -> B a
evalB x  | isClosedB x = (h2b .nf . b2h) x
evalB _ = Vb e

evalX :: (Cat a) => X a -> X a
evalX x = (b2x . evalB . x2b) x

evalS :: (Cat a) => S a -> S a
evalS x = (b2s . evalB . s2b) x

evalT :: T->T
evalT = x2t . evalX . t2x

evalN :: N->N
evalN = x2t . evalX . t2x

infixr 5 :->
data ST = O | ST :-> ST deriving (Eq,Read,Show) 

instance Cat ST where
  e = O
  c (x,y) = (x:->y)
  c' (x:->y) = (x,y)

st :: Cat a => a->ST
st = view

genCat :: Cat t => t -> [t]
genCat n | e_ n = [n]
genCat n | c_ n = [
    c (x,y) | k<-nums (s' n), 
              x<-genCat k, 
              y<-genCat (s' (sub n k))
  ]

genCatX :: Cat a => a -> [X a]
genCatX  = filter isClosedX . map t2x . genCat

genCatB :: Cat a => a -> [B a]
genCatB  = filter isClosedB . map t2b . genCat

genOpenX :: Cat a => a -> [X a]
genOpenX l = map t2x (nums l)

genClosedX l = filter isClosedX (genOpenX l)

genOpenB :: Cat a => a -> [B a]
genOpenB a = (map x2b . genOpenX) a

genClosedB :: Cat a => a -> [B a]
genClosedB a = (map x2b . genClosedX) a

ranCat :: (Cat t, RandomGen g) => 
          (N ->t) -> Int -> g -> (t, g)
ranCat tf size g = (bt2c bt,g') where
  (bt,g') = randomBinaryTree size g
  bt2c (Leaf ()) = tf 0
  bt2c (Branch l r) = c (bt2c l,bt2c r)

ranCat1 tf size seed = 
  fst (ranCat tf size (mkStdGen seed))

ranOpenX tf size g = (t2x r,g') where
  (r,g') = ranCat tf size g

ranOpen1X tf size seed = t2x (ranCat1 tf size seed)

ranClosedX tf size g =  
  if isClosedX x then x else ranClosedX tf size g' where
    (a,g') = ranCat tf size g
    x = t2x a

ranClosed1X tf size seed = ranClosedX tf size g where
  g = mkStdGen seed


