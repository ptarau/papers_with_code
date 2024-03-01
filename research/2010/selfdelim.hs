module SelfDelim where
import Data.List

type N = Integer

cons :: N->N->N
cons x y  = (2^x)*(2*y+1)

hd :: N->N
hd n | n>0 = if odd n then 0 else 1+hd  (n `div` 2)

tl :: N->N
tl n = n `div` 2^((hd n)+1)

nat2fun :: N->[N]
nat2fun 0 = []
nat2fun n = hd n : nat2fun (tl n)
 
fun2nat :: [N]->N  
fun2nat [] = 0
fun2nat (x:xs) = cons x (fun2nat xs)

data Iso a b = Iso (a->b) (b->a)

from (Iso f _) = f
to (Iso _ g) = g

compose :: Iso a b -> Iso b c -> Iso a c
compose (Iso f g) (Iso f' g') = Iso (f'.f) (g.g')
itself = Iso id id
invert (Iso f g) = Iso g f

type Hub = [N]

type Encoder a = Iso a Hub

with :: Encoder a->Encoder b->Iso a b
with this that = compose this (invert that)

as :: Encoder a -> Encoder b -> b -> a
as that this thing = to (with that this) thing

borrow_from :: Encoder a -> (a -> a -> a) -> 
               Encoder b -> b -> b -> b
borrow_from other op this x y = 
       borrow2 (with other this) op x y
borrow2 (Iso f g) h x y = f (h (g x) (g y))

fun :: Encoder [N]
fun = itself

nat :: Encoder N
nat = Iso nat2fun fun2nat

bits :: Encoder [N]
bits = compose (Iso bits2nat nat2bits) nat

nat2bits = init . (to_base 2) . succ
    
to_base base n = d : 
  if q==0 then [] else (to_base base q) where
    (q,d) = quotRem n base
    
bits2nat bs = pred (from_base 2 (bs ++ [1]))

from_base base [] = 0
from_base base (x:xs) | x>=0 && x<base = 
  x+base*(from_base base xs)

to_elias :: N -> [N]
to_elias n = (to_eliasx (succ n))++[0]

to_eliasx 1 = []
to_eliasx n = xs where
  bs=to_lbits n
  l=(genericLength bs)-1
  xs = if l<2 then bs else (to_eliasx l)++bs

from_elias :: [N] -> (N, [N])
from_elias bs = (pred n,cs) where 
  (n,cs)=from_eliasx 1 bs

from_eliasx n (0:bs) = (n,bs)
from_eliasx n (1:bs) = r where 
  hs=genericTake n bs
  ts=genericDrop n bs
  n'=from_lbits (1:hs)
  r=from_eliasx n' ts 

to_lbits = reverse . (to_base 2)

from_lbits = (from_base 2) . reverse

elias :: Encoder [N]
elias = compose (Iso (fst . from_elias) to_elias) nat

data T = H [T] deriving (Eq,Ord,Read,Show)

unrank f n = H (unranks f (f n))
unranks f ns = map (unrank f) ns

rank g (H ts) = g (ranks g ts)
ranks g ts = map (rank g) ts

tsize = rank (\xs->1 + (sum xs))

hylo :: Iso b [b] -> Iso T b
hylo (Iso f g) = Iso (rank g) (unrank f)

hylos :: Iso b [b] -> Iso [T] [b]
hylos (Iso f g) = Iso (ranks g) (unranks f)

hff :: Encoder T
hff = compose (hylo nat) nat

hffs :: Encoder T
hffs = Iso hff2fun fun2hff

fun2hff ns = H (map (as hff nat) ns)
hff2fun (H hs) = map (as nat hff) hs

hff_pars :: Encoder [N]
hff_pars = compose (Iso pars2hff hff2pars) hff

pars2hff cs = parse_pars 0 1 cs

parse_pars l r cs | newcs == [] = t where
  (t,newcs)=pars_expr l r cs

pars_expr l r (c:cs) | c==l = ((H ts),newcs) where 
  (ts,newcs) = pars_list l r cs    
  pars_list l r (c:cs) | c==r = ([],cs)
  pars_list l r (c:cs) = ((t:ts),cs2) where 
    (t,cs1)=pars_expr l r (c:cs)
    (ts,cs2)=pars_list l r cs1

hff2pars = collect_pars 0 1

collect_pars l r (H ns) =
  [l]++ (concatMap (collect_pars l r) ns)++[r] 

nat2parnat n = as nat bits (as hff_pars nat n)

parnat2nat n = as nat hff_pars (as bits nat n)

sparses_to m = [n|n<-[0..m-1],
  (genericLength (as hff_pars nat n)) 
  <
  (genericLength (as elias nat n))]

hff_bitsize n= sum (map size [0..2^n-1]) where
   size k=genericLength (as hff_pars nat k) 
elias_bitsize n= sum (map size [0..2^n-1]) where
   size k=genericLength (as elias nat k)    
bitsize n= sum (map size [0..2^n-1]) where
   size k=genericLength (as bits nat k)    

info_density_hff n = (bitsize n) / (hff_bitsize n)

info_density_elias n = (bitsize n) / (elias_bitsize n)

relative_density_hff n = (elias_bitsize n) / (hff_bitsize n)

nat2sfun n = nat2self (as fun nat) n   

nat2self f n = (to_elias l) ++ 
  concatMap to_elias ns where
    ns = f n
    l=genericLength ns

self2nat g ts = (g xs,ts') where 
  (l,ns) = from_elias ts
  (xs,ts')=take_from_elias l ns

  take_from_elias 0 ns = ([],ns) 
  take_from_elias k ns = ((x:xs),ns'') where
     (x,ns')=from_elias ns
     (xs,ns'')=take_from_elias (k-1) ns'
  
sfun2nat ns = xs where 
  (xs,[])=self2nat (as nat fun) ns

kraft_sum m = sum (map kraft_term [0..m-1])

kraft_term n= 1 / (2 ** l) where l = parsize n

parsize = genericLength . (as hff_pars nat)

kraft_check m = kraft_sum m <= 1

cat n = (f (2*n)) `div` ((f (n+1)) * (f n)) where f n=product [1..n]

log2 x = (log x)/(log 2) 
catk n = 1 / ((log2 (realToFrac (cat n))) / (realToFrac n))

