module ISO where
import Data.List
import Data.Bits
import Data.Graph
import Data.Char
import Array
import Ratio
import Random
import Data.Graph.Inductive
import Graphics.Gnuplot.Simple
import Funsat.Solver
import Funsat.Types hiding (with)
import Data.Set hiding (map, filter, union, partition)

data Iso a b = Iso (a->b) (b->a)

from (Iso f _) = f
to (Iso _ g) = g

compose :: Iso a b -> Iso b c -> Iso a c
compose (Iso f g) (Iso f' g') = Iso (f' . f) (g . g')
itself = Iso id id
invert (Iso f g) = Iso g f

type Auto a = Iso a a

dress :: Auto a -> Iso a b -> Iso a b
dress aa ab = compose aa ab

borrow :: Iso t s -> (t -> t) -> s -> s
borrow (Iso f g) h x = f (h (g x))
borrow2 (Iso f g) h x y = f (h (g x) (g y))
borrowN (Iso f g) h xs = f (h (map g xs))

lend :: Iso s t -> (t -> t) -> s -> s
lend = borrow . invert
lend2 = borrow2 . invert
lendN = borrowN . invert

fit :: (b -> c) -> Iso a b -> a -> c
fit op iso x = op ((from iso) x)

retrofit :: (a -> c) -> Iso a b -> b -> c
retrofit op iso x = op ((to iso) x)

type N = Integer
type Root = [N]

type Encoder a = Iso a Root

with :: Encoder a->Encoder b->Iso a b
with this that = compose this (invert that)

as :: Encoder a -> Encoder b -> b -> a
as that this thing = to (with that this) thing

borrow_from :: Encoder b -> (b -> b) ->
               Encoder a -> a -> a

borrow_from lender f borrower = 
  (as borrower lender) . f . (as lender borrower)

borrow_from2 :: Encoder a -> (a -> a -> a) -> 
                Encoder b -> b -> b -> b

borrow_from2 lender op borrower x y = 
    as borrower lender r where
       x'= as lender borrower x
       y'= as lender borrower y
       r = op x' y'

fun :: Encoder [N]
fun = itself

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

nat :: Encoder N
nat = Iso nat2fun fun2nat

app 0 ys = ys
app xs ys = cons (hd xs) (app (tl xs) ys)

unpair z = (hd (z+1),tl (z+1))
pair (x,y) = (cons x y)-1

cpair  (0,0)  = 0
cpair  (0,y)  = cons e (cpair (y,0))
cpair  (x,y) = cons (hd x) (cpair (y,(tl x)))  
 
cunpair 0 = (0,0)
cunpair z = (cons (hd z) x,y) where (y,x)=cunpair (tl z)

mset :: Encoder [N]
mset = Iso mset2fun fun2mset

mset2fun = to_diffs . sort . (map must_be_nat)

to_diffs xs = zipWith (-) (xs) (0:xs)

must_be_nat n | n>=0 = n

fun2mset ns = tail (scanl (+) 0 (map must_be_nat ns)) 

set2fun xs | is_set xs = shift_tail pred (mset2fun xs)

shift_tail _ [] = []
shift_tail f (x:xs) = x:(map f xs)

is_set ns = ns==nub ns

fun2set = (map pred) . fun2mset . (map succ)

set2fun' = (map pred) . mset2fun . (map succ)

set :: Encoder [N]
set = Iso set2fun fun2set

nat_set = Iso nat2set set2nat 

nat2set n | n>=0 = nat2exps n 0 where
  nat2exps 0 _ = []
  nat2exps n x = 
    if (even n) then xs else (x:xs) where
      xs=nat2exps (n `div` 2) (succ x)

set2nat ns | is_set ns = sum (map (2^) ns)

nat' :: Encoder N
nat' = compose nat_set set

nat2mset = as mset nat
mset2nat = as nat mset 

nat2pmset 0 = []
nat2pmset n = map (to_pos_in (h:ts)) (to_factors (n+1) h ts) where
  (h:ts)=genericTake (n+1) primes
  
to_pos_in xs x = fromIntegral i where
   Just i=elemIndex x xs

pmset2nat [] = 0
pmset2nat ns = (product ks)-1 where
  ks=map (from_pos_in ps) ns
  ps=primes

from_pos_in xs n = xs !! (fromIntegral n)

pmset :: Encoder [N]
pmset = compose (Iso pmset2nat nat2pmset) nat

pnats :: Encoder [N]
pnats = compose (Iso (as mset fun) (as fun mset)) pmset

pset :: Encoder [N]
pset = compose (Iso (as fun set) (as set fun)) pnats

mprod = borrow_from2 mset (++) nat

mprod_alt n m = as nat mset ((as mset nat n) ++ (as mset nat m))

mexp n 0 = 0
mexp n k = mprod n (mexp n (k-1))

pmprod n m = as nat pmset ((as pmset nat n) ++ (as pmset nat m))

pmprod' n m = (n+1)*(m+1)-1

mprod' 0 _ = 0
mprod' _ 0 = 0
mprod' m n = (mprod (n-1) (m-1)) + 1

mexp' n 0 = 1
mexp' n k = mprod' n (mexp' n (k-1))

mgcd :: N -> N -> N
mgcd = borrow_from2 mset msetInter nat

mlcm :: N -> N -> N
mlcm = borrow_from2 mset msetUnion nat

mdiv :: N -> N -> N
mdiv = borrow_from2 mset msetDif nat

is_mprime p = []==[n|n<-[1..p-1],n `mdiv` p==0]

mprimes = filter is_mprime [1..]

rgcd 1 = 7
rgcd n | n>1 = n' + (gcd n n') where  n'=rgcd (pred n)

dgcd n = (rgcd (succ n')) - (rgcd n') where n'=succ n

rlcm 1 = 1
rlcm n | n>1 = n' + (lcm n n') where  n'=rlcm (pred n)

dlcm n = pred ((rlcm (succ n')) `div` (rlcm n')) where n'=succ n

plcd n = (tail . sort . nub . (map dgcd)) [0..n] 

plcm n = (tail . sort . nub . (map dlcm)) [0..n] 

rmlcm 1 = 1
rmlcm n | n>1 = n' + (mlcm n n') where  n'=rmlcm (pred n)

dmlcm n = pred ((rmlcm (succ n')) `div` (rmlcm n')) where n'=succ n

mplcm n = (tail . sort . nub . (map dmlcm)) [0..n] 

bits :: Encoder [N]
bits = compose (Iso bits2nat nat2bits) nat

nat2bits = drop_last . (to_base 2) . succ

bits2nat bs = pred (from_base 2 (bs ++ [1]))

drop_last =
    reverse . tail . reverse

bits1 :: Encoder [N]
bits1 = compose (Iso (from_base 2) (to_base 2)) nat

to_base base n = d : 
  (if q==0 then [] else (to_base base q)) where
     (q,d) = quotRem n base
    
from_base base [] = 0
from_base base (x:xs) | x>=0 && x<base = 
   x+base*(from_base base xs)

mirror = dress (Iso dual dual)
dual bs = map f bs where
  f 0=1
  f 1=0

bits' :: Encoder [N]
bits' = mirror bits

ndual = borrow_from bits dual nat

ndual' = (as nat bits) . (as bits' nat)

nat2gray :: N->N
nat2gray n= n `xor` (shiftR n 1)

gray2nat = borrow_from bits1 (scanr1 xor) nat

grayer :: Auto N
grayer = Iso nat2gray gray2nat
grayed = dress grayer

gray :: Encoder N
gray = compose grayer nat

bijnat :: N->Encoder [N]

bijnat a = compose (Iso (from_bbase a) (to_bbase a)) nat

from_bbase base xs = from_base' base (map succ xs)

from_base' base [] = 0
from_base' base (x:xs) | x>0 && x<=base = 
   x+base*(from_base' base xs)
   
to_bbase base n = map pred (to_base' base n)

to_base' _ 0 = []
to_base' base n = d' : ds where
   (q,d) = quotRem n base
   d'=if d==0 then base else d
   q'=if d==0 then q-1 else q
   ds=if q'==0 then [] else to_base' base q'

type Z = Integer
z:: Encoder Z
z = compose (Iso z2nat nat2z) nat

nat2z n = if even n then n `div` 2 else (-n-1) `div` 2
z2nat n = if n<0 then -2*n-1 else 2*n

nplus x y = borrow_from2 z (+) nat x y
nneg x = borrow_from z (\x->0-x) nat x

nprod = borrow_from2 z (*) nat

b x = pred x -- begin
o x = 2*x+0  -- bit 0
i x = 2*x+1  -- bit 1
e = 1        -- end

data D = E | O D | I D deriving (Eq,Ord,Show,Read)
data B = B D deriving (Eq,Ord,Show,Read)

funbits2nat :: B -> N
funbits2nat = bfold b o i e

bfold fb fo fi fe (B d) = fb (dfold d) where
  dfold E = fe
  dfold (O x) = fo (dfold x)
  dfold (I x) = fi (dfold x)

b' x = succ x
o' x | even x = x `div` 2
i' x | odd x = (x-1) `div` 2
e' = 1

nat2funbits :: N -> B
nat2funbits = bunfold b' o' i' e'

bunfold fb fo fi fe x = B (dunfold (fb x)) where
  dunfold n | n==fe = E
  dunfold n | even n = O (dunfold (fo n))
  dunfold n | odd n = I (dunfold (fi n))

funbits :: Encoder B
funbits = compose (Iso funbits2nat nat2funbits) nat

bsucc (B d) = B (dsucc d) where
  dsucc E = O E
  dsucc (O x) = I x
  dsucc (I x) = O (dsucc x) 

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

hfs :: Encoder T
hfs = compose (hylo nat_set) nat

hfs_union = borrow2 (with set hfs) union
hfs_succ = borrow (with nat hfs) succ
hfs_pred = borrow (with nat hfs) pred

ackermann = as nat hfs
inverse_ackermann = as hfs nat

hff :: Encoder T
hff = compose (hylo nat) nat

hffs :: Encoder [T]
hffs = Iso hffs2fun fun2hffs

fun2hffs ns =  (map (as hff nat) ns)
hffs2fun (hs) = map (as nat hff) hs

nat_mset = Iso nat2mset mset2nat

hfm :: Encoder T
hfm = compose (hylo nat_mset) nat

nat_pmset = Iso nat2pmset pmset2nat

hfpm :: Encoder T
hfpm = compose (hylo nat_pmset) nat

data UT a = At a | UT [UT a] deriving (Eq,Ord,Read,Show)

ulimit = 2^14

unrankU = unrankUL ulimit
unranksU = unranksUL ulimit

unrankUL l _ n | n>=0 && n<l = At n
unrankUL l f n = UT (unranksUL l f (f (n-l)))

unranksUL l f ns =  map (unrankUL l f) ns

rankU = rankUL ulimit
ranksU = ranksUL ulimit

rankUL l _ (At n) | n>=0 && n<l = n
rankUL l g (UT ts) = l+(g (ranksUL l g ts))

ranksUL l g ts = map (rankUL l g) ts

hyloU (Iso f g) = Iso (rankU g) (unrankU f)
hylosU (Iso f g) = Iso (ranksU g) (unranksU f)

uhfs :: Encoder (UT N)
uhfs = compose (hyloU nat_set) nat

uhff :: Encoder (UT N)
uhff = compose (hyloU nat) nat

unrankIU _ n | even n = At (n `div` 2) 
unrankIU f n = UT (unranksIU f (f  ((n-1) `div` 2)))

unranksIU f ns =  map (unrankIU f) ns

rankIU _ (At n) = 2*n
rankIU g (UT ts) = 1+2*(g (ranksIU g ts))

ranksIU g ts = map (rankIU g) ts

hyloIU (Iso f g) = Iso (rankIU g) (unrankIU f)
hylosIU (Iso f g) = Iso (ranksIU g) (unranksIU f)

iuhfs :: Encoder (UT N)
iuhfs = compose (hyloIU nat_set) nat

iuhff :: Encoder (UT N)
iuhff = compose (hyloIU nat) nat

fr 0 = [0]
fr n = f 1 n where
   f _ 0 = []
   f j k = (k `mod` j) : 
           (f (j+1) (k `div` j))

fl = reverse . fr

rf ns = sum (zipWith (*) ns factorials) where
  factorials=scanl (*) 1 [1..]

lf = rf . reverse

perm2nth ps = (l,lf ls) where 
  ls=perm2lehmer ps
  l=genericLength ls

perm2lehmer [] = []
perm2lehmer (i:is) = l:(perm2lehmer is) where
  l=genericLength [j|j<-is,j<i]  

nth2perm (size,n) = 
  apply_lehmer2perm (zs++xs) [0..size-1] where 
    xs=fl n
    l=genericLength xs
    k=size-l
    zs=genericReplicate k 0

apply_lehmer2perm [] [] = []
apply_lehmer2perm (n:ns) ps@(x:xs) = 
   y : (apply_lehmer2perm ns ys) where
   (y,ys) = pick n ps

pick i xs = (x,ys++zs) where 
  (ys,(x:zs)) = genericSplitAt i xs

lehmer2perm ls = apply_lehmer2perm ls [0..(genericLength ls)-1]

sf n = rf (genericReplicate n 1)

to_sf n = (k,n-m) where 
  k=pred (head [x|x<-[0..],sf x>n])
  m=sf k

nat2perm 0 = []
nat2perm n = nth2perm (to_sf n)

perm2nat ps = (sf l)+k where 
  (l,k) = perm2nth ps

perm :: Encoder [N]
perm = compose (Iso perm2nat nat2perm) nat

nat2hfp = unrank nat2perm
hfp2nat = rank perm2nat

hfp :: Encoder T
hfp = compose (Iso hfp2nat nat2hfp) nat

rerootWith a (H []) = a
rerootWith a (H bs) = H (map (rerootWith a) bs)

nreroot t = borrow_from2 t rerootWith nat

weedWith _ (H []) = H []
weedWith w b | w == b = H [] 
weedWith w (H bs) = H (map (weedWith w) bs)

nweed t = borrow_from2 t weedWith nat

trimEmpty (H []) = H []
trimEmpty (H xs) = H (trimEmpties xs)

trimEmpties [] = []
trimEmpties ((H []):xs) = trimEmpties xs
trimEmpties (x:xs)=(trimEmpty x):trimEmpties xs

ntrim t = borrow_from t trimEmpty nat

nat2kpoly k n = filter (\p->0/=fst p) ps where 
  ns=to_base k n
  l=genericLength ns
  is=[0..l-1]
  ps=zip ns is 

kpoly2nat k ps = sum (map (\(d,e)->d*k^e) ps)

data HB a = HB a [HB a]  deriving (Eq,Ord,Show,Read)

nat2hb :: N->N->[HB N]

nat2hb _k 0 = [] 
nat2hb k n | n<k = [HB n []]
nat2hb k n = gs where 
  ps'=nat2kpoly k n
  gs=map (nat2hb1 k) ps'
  nat2hb1 k (d,e) = HB d (nat2hb k e)
 
hb2nat :: N -> [HB N] -> N
 
hb2nat k [] = 0
hb2nat k ts = kpoly2nat k ps where
  ps=map (hb2nat1 k) ts
  hb2nat1 k (HB d ts) = (d,hb2nat k ts)

hb :: N->Encoder [HB N]
hb k = compose (Iso (hb2nat k) (nat2hb k)) nat

goodsteinStep k n = (hb2nat (k+1) (nat2hb k n)) - 1

goodsteinSeq _ 0 = []
goodsteinSeq k n = n:(goodsteinSeq (k+1) m) where 
  m=goodsteinStep k n
  
goodstein m = goodsteinSeq 2 m

iterates f b n = reverse (takeWhile (<=n) (iterate f b))

to_fbase f b n | b>0 = reverse (spread (iterates f b n) n) 
spread [] n=[n]
spread (d:ds) n = q:spread ds r where (q,r)=quotRem n d

from_fbase f b ns | b>0 = sum (zipWith (*) ns (1:iterate f b))

to_sqbase b n | b>1 = to_fbase (^2) b n
from_sqbase b ns | b>1 = from_fbase (^2) b ns

to_3x1 b n |b>0 = to_fbase (\x->3*x+1) b n
from_3x1 b ns = from_fbase (\x->3*x+1) b ns

string :: Encoder String
string = compose (Iso string2nat nat2string) nat

base = 1+ord '~'- ord ' '
chr2ord c | c>=' ' && c<='~' = ord c - ord ' '

ord2chr o | o>=0 && o<base = chr (ord ' '+o)

string2nat cs = from_bbase 
  (fromIntegral base) 
  (map (fromIntegral . chr2ord) cs)

nat2string n = map 
  (ord2chr . fromIntegral) 
  (to_bbase (fromIntegral base) n)

cantor_pair (x,y) = (x+y)*(x+y+1) `div` 2+y

isqrt 0 = 0
isqrt n | n>0 = if k*k>n then k-1 else k where 
  k=iter n
  iter x = if abs(r-x)  < 2 
    then r 
    else iter r where r = step x
  d x y = x `div` y
  step x = d (x+(d n x)) 2

cantor_unpair z = (x,y) where
  i=(isqrt (8*z+1)-1) `div` 2
  x=(i*(3+i) `div` 2)-z
  y=z-(i*(i+1) `div` 2)

type N2 = (N,N)

cnat2 :: Encoder N2
cnat2 = compose (Iso cantor_pair cantor_unpair) nat

pepis_J x y  = pred ((2^x)*(succ (2*y)))

pepis_K n = two_s (succ n)

pepis_L n = (pred (no_two_s (succ n))) `div` 2
 
two_s n | even n = succ (two_s (n `div` 2))
two_s _ = 0

no_two_s n = n `div` (2^(two_s n))

pepis_pair (x,y) = pepis_J x y
pepis_unpair n = (pepis_K n,pepis_L n)

pepis_pair' (x,y) = (fun2nat (x:(nat2fun y)))-1

pepis_unpair' n = (x,fun2nat ns) where 
  (x:ns)=nat2fun (n+1) 

rpepis_pair (x,y) = pepis_pair (y,x)
rpepis_unpair n = (y,x) where (x,y)=pepis_unpair n

pnat2 :: Encoder N2
pnat2 = compose (Iso pepis_pair pepis_unpair) nat

rpnat2 :: Encoder N2
rpnat2 = compose (Iso rpepis_pair rpepis_unpair) nat

hpair (x,y) = z-1 where 
  hx=as hff nat x
  H hs =as hff nat y
  hz= H (hx:hs)
  z=as nat hff hz
    
hunpair z = (x,y) where
  H (hx:hs) = as hff nat (z+1)
  x=as nat hff hx
  y=as nat hff (H hs)

bitpair ::  N2 -> N
bitpair (i,j) = 
  set2nat ((evens i) ++ (odds j)) where
    evens x = map (2*) (nat2set x)
    odds y = map succ (evens y)

bitunpair :: N->N2  
bitunpair n = (f xs,f ys) where 
  (xs,ys) = partition even (nat2set n)
  f = set2nat . (map (`div` 2))

nat2 :: Encoder N2
nat2 = compose (Iso bitpair bitunpair) nat

pair2unord_pair (x,y) = fun2set [x,y]
unord_pair2pair [a,b] = (x,y) where 
  [x,y]=set2fun [a,b]   

unord_unpair = pair2unord_pair . bitunpair
unord_pair = bitpair . unord_pair2pair

set2 :: Encoder [N]
set2 = compose (Iso unord_pair2pair pair2unord_pair) nat2

set2' :: Encoder [N]
set2' = compose (Iso unord_pair unord_unpair) nat

pair2mset_pair (x,y) = (a,b) where [a,b]=fun2mset [x,y]
mset_unpair2pair (a,b) = (x,y) where [x,y]=mset2fun [a,b]

mset_unpair = pair2mset_pair . bitunpair
mset_pair = bitpair . mset_unpair2pair

mset2 :: Encoder N2
mset2 = compose (Iso mset_unpair2pair pair2mset_pair) nat2

type Z2 = (Z,Z)

z2 :: Encoder Z2
z2 = compose (Iso zpair zunpair) nat

zpair (x,y) = (nat2z . bitpair) (z2nat x,z2nat y)
zunpair z = (nat2z n,nat2z m) where (n,m)= (bitunpair . z2nat) z

mz2 :: Encoder Z2
mz2 = compose (Iso mzpair mzunpair) nat

mzpair (x,y) = (nat2z . mset_pair) (z2nat x,z2nat y)
mzunpair z = (nat2z n,nat2z m) where (n,m)= (mset_unpair . z2nat) z

gauss_sum (ab,cd) = mzpair (a+b,c+d) where
  (a,b)=mzunpair ab
  (c,d)=mzunpair cd

gauss_dif (ab,cd) = mzpair (a-b,c-d) where
  (a,b)=mzunpair ab
  (c,d)=mzunpair cd
  
gauss_prod (ab,cd) = mzpair (a*c-b*d,b*c+a*d) where
  (a,b)=mzunpair ab
  (c,d)=mzunpair cd

bitlift x = bitpair (x,0)
bitlift' = (from_base 4) . (to_base 2)

bitclip = fst . bitunpair
bitclip' = (from_base 2) . (map (`div` 2)) . (to_base 4) . (*2)

bitpair' (x,y) = (bitpair (x,0))   +   (bitpair(0,y))
xbitpair (x,y) = (bitpair (x,0)) `xor` (bitpair (0,y))
obitpair (x,y) = (bitpair (x,0))  .|.  (bitpair (0,y))

pair_product (x,y) = a+b where
  x'=bitpair (x,0)
  y'=bitpair (0,y)
  ab=x'*y'
  (a,b)=bitunpair ab

inflate 0 = 0
inflate n = (db . db . inflate . hf) n .|. parity n

deflate 0 = 0
deflate n = (db . deflate . hf . hf) n .|. parity n

deflate' = hf . deflate . db
inflate' = db . inflate

pproduct x y = a + b where
  x'=inflate x
  y'=inflate' y
  ab=x'*y'
  a=deflate ab
  b=deflate' ab

bitpair'' (x,y) = mset_pair (min x y,x+y) 

bitpair''' (x,y) = unord_pair [min x y,x+y+1]

mset_pair' (a,b) = bitpair (min a b, (max a b) - (min a b)) 

mset_pair'' (a,b) = unord_pair [min a b, (max a b)+1]

unord_pair' [a,b] = bitpair (min a b, (max a b) - (min a b) -1) 

unord_pair'' [a,b] = mset_pair (min a b, (max a b)-1)

data CList = Atom N | Cons CList CList 
  deriving (Eq,Ord,Show,Read)

to_atom n = 2*n
from_atom a | is_atom a = a `div` 2
is_atom n = even n  && n>=0

is_cons n = odd n && n>0
decons z | is_cons z = pepis_unpair ((z-1) `div` 2)
conscell x y = 2*(pepis_pair (x,y))+1

nat2cons n | is_atom n = Atom (from_atom n)
nat2cons n | is_cons n = 
  Cons (nat2cons hd) 
       (nat2cons tl) where
    (hd,tl) = decons n     

cons2nat (Atom a) =  to_atom a
cons2nat (Cons h t) = conscell (cons2nat h) (cons2nat t)

clist :: Encoder CList
clist = compose (Iso cons2nat nat2cons) nat

parity :: N->N
parity x = x .&. 1

altpair c (x,y) | (parity x)==(parity y) = c (x,y)
altpair c (x,y) = c (y,x)

altunpair d z = r where 
    (x,y)=d z
    r=if parity x==parity y then (x,y) else (y,x)

scnat2 :: Encoder N2
scnat2 = compose (Iso cantor_pair cantor_unpair) nat

data Term var const = 
   Var var | 
   Fun const [Term var const] 
   deriving (Eq,Ord,Show,Read)

type NTerm = Term N N

nats = fun'

nterm2code :: Term N N -> N

nterm2code (Var i) = 2*i
nterm2code (Fun cName args) = code where
  cs=map nterm2code args
  fc=as nat nats (cName:cs)
  code = 2*fc-1

code2nterm :: N -> Term N N

code2nterm n | even n = Var (n `div` 2) 
code2nterm n = Fun cName args where
  k = (n+1) `div` 2
  cName:cs = as nats nat k
  args = map code2nterm cs

nterm :: Encoder NTerm
nterm = compose (Iso nterm2code code2nterm) nat

type STerm = Term N String

sterm2code :: Term N String -> N

sterm2code (Var i) = 2*i
sterm2code (Fun name args) = code where
  cName=as nat string name
  cs=map sterm2code args
  fc=as nat nats (cName:cs)
  code=2*fc-1

code2sterm :: N -> Term N String

code2sterm n | even n = Var (n `div` 2) 
code2sterm n = Fun name args where
  k = (n+1) `div` 2
  cName:cs = as nats nat k
  name = as string nat cName
  args = map code2sterm cs

sterm :: Encoder STerm
sterm = compose (Iso sterm2code code2sterm) nat

nterm2bits = as bits nterm
bits2nterm = as nterm bits

sterm2bits = as bits sterm
bits2sterm = as sterm bits

xhd :: N->N->N
xhd b n | b>1 && n>0 = 
  if n `mod` b > 0 then 0 else 1+xhd b (n `div` b)

xtl :: N->N->N
xtl b n = y-1 where
  y'= n `div` b^(xhd b n)
  y=rebase b (b-1) y'

rebase fromBase toBase n =  toBase*q + r where
  (q,r)=n `quotRem` fromBase
    

xcons :: N->N->N->N
xcons b x y | b>1 = (b^x)*(y'+1) where
  y'=rebase (b-1) b y

xunpair b n = (xhd b n',xtl b n') where n'=n+1

xpair b (x,y) = (xcons b x y)-1

xsplit _ 0 = []
xsplit b x = xhd b x : xsplit b (xtl b x)
 
xfuse _ [] = 0
xfuse b (x:xs) = xcons b x (xfuse b xs)

xbij k l n = xfuse l (xsplit k n) 

ybij m | m>3 = (xbij 3 m) . (xbij m 2)

fmset2nat pairingf ms = m where  
  mss= group (sort ms) 
  xs=map (pred . genericLength) mss
  zs=map head mss
  ys=set2fun zs
  ps=zip xs ys
  ns=map pairingf ps 
  m=fun2nat ns

fnat2mset unpairingf m = rs where
   ns=nat2fun m
   ps=map unpairingf ns
   (xs,ys)=unzip ps
   xs'=map succ xs
   zs=fun2set ys
   f k x = genericTake k (repeat x) 
   rs = concat (zipWith f xs' zs)

bmset2nat = fmset2nat bitpair
nat2bmset = fnat2mset bitunpair

bmset2nat' = fmset2nat pepis_pair
nat2bmset' = fnat2mset pepis_unpair

bmset :: Encoder [N]
bmset = compose (Iso bmset2nat nat2bmset) nat

bmset' :: Encoder [N]
bmset' = compose (Iso bmset2nat' nat2bmset') nat

nat_bmset = Iso nat2bmset bmset2nat

hfbm :: Encoder T
hfbm = compose (hylo nat_bmset) nat

nat_bmset' = Iso nat2bmset' bmset2nat'

hfbm' :: Encoder T
hfbm' = compose (hylo nat_bmset') nat

nats2goedel ns =  product xs where
  xs=zipWith (^) primes ns

goedel2nats n = combine ds xs where
  pss=group (to_primes n)
  ps=map head pss
  xs=map genericLength pss
  ds=as fun set (map pi' ps)
  
  combine [] [] = []
  combine (b:bs) (x:xs) = 
    replicate (fromIntegral b) 0 ++ x:(combine bs xs)

pi' p | is_prime p= to_pos_in primes p 

goedel :: Encoder [N]
goedel = compose (Iso nats2g g2nats) nat

nats2g [] = 0
nats2g ns = pred (nats2goedel (z:ns)) where
  z=countZeros (reverse ns)

g2nats 0 = []  
g2nats n = ns ++ (replicate (fromIntegral z) 0) where 
  (z:ns)=goedel2nats (succ n)
    
countZeros (0:ns) = 1+countZeros ns
countZeros _ = 0

goedel' :: Encoder [N]
goedel' = compose (Iso nats2gnat gnat2nats) nat

nats2gnat = pmset2nat . (as mset fun)

gnat2nats = (as fun mset) . nat2pmset

data BT a = B0 | B1 | D a (BT a) (BT a) 
             deriving (Eq,Ord,Read,Show)

data BDD a = BDD a (BT a) deriving (Eq,Ord,Read,Show)

unfold_bdd :: N2 -> BDD N
unfold_bdd (n,tt) = BDD n bt where 
  bt=if tt<max then split_with bitunpair n tt
     else error 
       ("unfold_bdd: last arg "++ (show tt)++
       " should be < " ++ (show max))
     where max = 2^2^n

split_with _ 0 0 =  B0
split_with _ 0 1 =  B1
split_with f n tt | n>0 = 
   D k (split_with f k tt1) 
       (split_with f k tt2) where
    k=pred n
    (tt1,tt2)=f tt

fold_bdd :: BDD N -> N2
fold_bdd (BDD n bt) = 
  (n,fuse_with bitpair bt) where
    fuse_with rf B0 = 0
    fuse_with rf B1 = 1
    fuse_with rf (D _ l r) = 
      rf (fuse_with rf l,fuse_with rf r)

eval_bdd (BDD n bt) = eval_with_mask (bigone n) n bt
 
eval_with_mask _ _ B0 = 0 
eval_with_mask m _ B1 = m
eval_with_mask m n (D x l r) = 
  ite_ (var_mn m n x) 
         (eval_with_mask m n l) 
         (eval_with_mask m n r)
         
var_mn mask n k = mask `div` (2^(2^(n-k-1))+1)
bigone nvars = 2^2^nvars - 1         

ite_ x t e = ((t `xor` e).&.x) `xor` e

bsum 0 = 0
bsum n | n>0 = bsum1 (n-1)

bsum1 0 = 2
bsum1 n | n>0 = bsum1 (n-1)+ 2^2^n

bsums = map bsum [0..]

to_bsum n = (k,n-m) where 
  k=pred (head [x|x<-[0..],bsum x>n])
  m=bsum k

nat2bdd n = unfold_bdd (k,n_m) where (k,n_m)=to_bsum n

bdd2nat bdd@(BDD nv _) = (bsum nv)+tt where
  (_,tt) =fold_bdd bdd

pbdd :: Encoder (BDD N)
pbdd = compose (Iso bdd2nat nat2bdd) nat

ev_bdd2nat bdd@(BDD nv _) = (bsum nv)+(eval_bdd bdd)

bdd :: Encoder (BDD N)
bdd = compose (Iso ev_bdd2nat nat2bdd) nat

bdd_reduce (BDD n bt) = BDD n (reduce bt) where
  reduce B0 = B0
  reduce B1 = B1
  reduce (D _ l r) | l == r = reduce l
  reduce (D v l r) = D v (reduce l) (reduce r)

unfold_rbdd = bdd_reduce . unfold_bdd  

nat2rbdd = bdd_reduce . nat2bdd 

rbdd :: Encoder (BDD N)
rbdd = compose (Iso ev_bdd2nat nat2rbdd) nat

bdd_size (BDD _ t) = 1+(size t) where
  size B0 = 1
  size B1 = 1
  size (D _ l r) = 1+(size l)+(size r)

robdd_size (BDD _ t) = 1+(rsize t) where
  rsize = genericLength . nub . rbdd_nodes
  rbdd_nodes B0 = [B0]
  rbdd_nodes B1 = [B1]
  rbdd_nodes (D v l r) = 
    [(D v l r)] ++ (rbdd_nodes l) ++ (rbdd_nodes r)

to_bdd vs tt | 0<=tt && tt <= m = 
  BDD n (to_bdd_mn vs tt m n) where
    n=genericLength vs
    m=bigone n
to_bdd _ tt = error 
   ("bad arg in to_bdd=>" ++ (show tt)) 

to_bdd_mn []      0 _ _ = B0
to_bdd_mn []      _ _ _ = B1
to_bdd_mn (v:vs) tt m n = D v l r where
  (f1,f0)=unpair_mn v m n tt
  l=to_bdd_mn vs f1 m n
  r=to_bdd_mn vs f0 m n
  
unpair_mn v m n tt = (f1,f0) where
  cond=var_mn m n v
  f0= (m `xor` cond) .&. tt
  f1= cond .&. tt

to_rbdd vs tt = bdd_reduce (to_bdd vs tt)
from_bdd bdd = eval_bdd bdd

nat2bdd0 n = b where 
  b=to_bdd (reverse [0..k-1]) m_n
  (k,m_n)=to_bsum n

nat2bddn n = b where 
  b=to_bdd [0..k-1] m_n
  (k,m_n)=to_bsum n

bddn :: Encoder (BDD N)
bddn = compose (Iso ev_bdd2nat nat2bddn) nat

to_min_bdd n t = search_bdd min n t

search_bdd f n tt = snd (foldl1 f 
 (map (sized_rbdd tt) (all_permutations n))) where
    sized_rbdd tt vs = (robdd_size b,b) where 
      b=to_rbdd vs tt
 
all_permutations n = if n==0 then [[]] else
  [nth2perm (n,i)|i<-[0..(factorial n)-1]] where
     factorial n=foldl1 (*) [1..n]

data MT a = Lf a | M a (MT a) (MT a) deriving (Eq,Ord,Read,Show)
data MTBDD a = MTBDD a a (MT a) deriving (Show,Eq)

to_mtbdd m n tt = MTBDD m n r where 
  mlimit=2^m
  nlimit=2^n
  ttlimit=mlimit^nlimit
  r=if tt<ttlimit 
    then (to_mtbdd_ mlimit n tt)
    else error 
      ("bt: last arg "++ (show tt)++
      " should be < " ++ (show ttlimit))

to_mtbdd_ mlimit n tt|(n<1)&&(tt<mlimit) = Lf tt
to_mtbdd_ mlimit n tt = (M k l r) where 
   (x,y)=bitunpair tt
   k=pred n
   l=to_mtbdd_ mlimit k x
   r=to_mtbdd_ mlimit k y

from_mtbdd (MTBDD m n b) = from_mtbdd_ (2^m) n b

from_mtbdd_ mlimit n (Lf tt)|(n<1)&&(tt<mlimit)=tt
from_mtbdd_ mlimit n (M _ l r) = tt where 
   k=pred n
   x=from_mtbdd_ mlimit k l
   y=from_mtbdd_ mlimit k r
   tt=bitpair (x,y)

lTie xs ys = xs ++ ys

lZip [] [] = []
lZip (x:xs) (y:ys) = x:y:(lZip xs ys)

bdd2plist (BDD _ b) = bt2plist b where
  bt2plist B0 = [0]
  bt2plist B1 = [1]
  bt2plist (D _ l r) = (bt2plist l) ++ (bt2plist r)  

data PL a =  Sc a | Tie (PL a) (PL a) | Zip (PL a) (PL a) 
  deriving (Eq,Show,Read)

bdd2pl f (BDD _ b) = bt2pl f b where
  bt2pl _ B0 = Sc 0
  bt2pl _ B1 = Sc 1
  bt2pl f (D _ l r) = f (bt2pl f l) (bt2pl f r)
  
bdd2zip b = bdd2pl Zip b

bdd2tie b = bdd2pl Tie b

flattenPL (Sc a)= [a]
flattenPL (Tie x y) = lTie (flattenPL x) (flattenPL y)
flattenPL (Zip x y) = lZip (flattenPL x) (flattenPL y)

depthPL (Sc _)= 0
depthPL (Tie x _) = 1+(depthPL x)
depthPL (Zip x _) = 1+(depthPL x)

powerZip :: Encoder (PL N)
powerZip = compose (Iso pl2nat nat2zip) nat

powerTie :: Encoder (PL N)
powerTie = compose (Iso pl2nat nat2tie) nat

nat2zip n = bdd2pl Zip (as bdd nat n)
nat2tie n = bdd2pl Tie (as bddn nat n)

pl2nat pl = bsum (depthPL pl)+(as nat bits1 (flattenPL pl))

zip2tie = as powerTie powerZip
tie2zip = as powerZip powerTie

rev (Sc x) = Sc x
rev (Tie x y) = Tie (rev y) (rev x)
rev (Zip x y) = Zip (rev y) (rev x)

tierev = borrow_from powerTie rev nat
ziprev = borrow_from powerZip rev nat

tieSucc = borrow_from nat succ powerTie
tiePred = borrow_from nat pred powerTie
tieSum = borrow_from2 nat (+) powerTie

zipSucc = borrow_from nat succ powerZip
zipPred = borrow_from nat pred powerZip
zipSum = borrow_from2 nat (+) powerZip

to_tuple k n | k>0 && n>=0 = map (from_base 2) (
    transpose (
      map (to_maxbits k) (
        to_base (2^k) n
      )
    )
  )

from_tuple ns = from_base (2^k) (
    map (from_base 2) (
      transpose (
        map (to_maxbits l) ns
      )
    )
  ) where 
      k=genericLength ns
      l=max_bitcount ns

ftuple2nat [] = 0
ftuple2nat ns = succ (pepis_pair (pred k,t)) where
  k=genericLength ns 
  t=from_tuple ns

nat2ftuple 0 = []
nat2ftuple kf = to_tuple (succ k) f where 
  (k,f)=pepis_unpair (pred kf)

fun' :: Encoder [N]
fun' = compose (Iso ftuple2nat nat2ftuple) nat

nat_fun' = Iso nat2ftuple ftuple2nat

hff' :: Encoder T
hff' = compose (hylo nat_fun') nat

mset2nat' = ftuple2nat . mset2fun
nat2mset' = fun2mset . nat2ftuple

nat_mset' = Iso nat2mset' mset2nat' 

mset' :: Encoder [N]
mset' = compose (invert nat_mset') nat

set2nat' = ftuple2nat . set2fun
nat2set' = fun2set . nat2ftuple 

nat_set' = Iso nat2set' set2nat' 

set' :: Encoder [N]
set' = compose (invert nat_set') nat


hfs' :: Encoder T
hfs' = compose (hylo nat_set') nat

hfm' :: Encoder T
hfm' = compose (hylo nat_mset') nat

hd' = head . nat2ftuple
tl' = ftuple2nat . tail . nat2ftuple
cons' h t  = ftuple2nat (h:(nat2ftuple t))

pair' (x,y) = (cons' x y)-1
unpair' z = (hd' z', tl' z') where z'=z+1

pairKL k l (x,y) = from_tuple (xs ++ ys) where
   xs = to_tuple k x
   ys = to_tuple l y
   
unpairKL k l z = (x,y) where 
  zs=to_tuple (k+l) z
  xs=genericTake k zs
  ys=genericDrop k zs
  x=from_tuple xs
  y=from_tuple ys


nat2mat 0 = []
nat2mat n = rows where
  n'=pred n
  k=matK n'
  rows=to_tuple k n'

matK = isqrt . genericLength . (to_base 2)

mat2nat [] = 0
mat2nat ns = succ (from_tuple ns)
  

digraph2set ps = map bitpair ps
set2digraph ns = map bitunpair ns

digraph :: Encoder [N2]
digraph = compose (Iso digraph2set set2digraph) set

digraph2set' ps = map pepis_pair ps
set2digraph' ns = map pepis_unpair ns

digraph' :: Encoder [N2]
digraph' = compose (Iso digraph2set' set2digraph') set

graph2mset ps = map mset_pair ps
mset2graph ns = map mset_unpair ns

graph :: Encoder [N2]
graph = compose (Iso graph2mset mset2graph) set

mdigraph :: Encoder [N2]
mdigraph = compose (Iso digraph2set set2digraph) fun

mgraph :: Encoder [N2]
mgraph = compose (Iso graph2mset mset2graph) fun

set2hypergraph = map (nat2set . succ)
hypergraph2set = map (pred . set2nat)

hypergraph :: Encoder [[N]]
hypergraph = compose (Iso hypergraph2set set2hypergraph) set

bipartite :: Encoder [N2]
bipartite = compose (Iso bipartite2hyper hyper2bipartite) hypergraph
 
hyper2bipartite xss = xs where
  l=genericLength xss
  xs=[(fromIntegral (2*i+1),fromIntegral (2*x))|i<-[0..l-1],x<-xss!!i]

bipartite2hyper xs = xss where
  pss = groupBy (\x y->fst x== fst y)  xs
  xss = map (map (hf . snd)) pss
  hf x = x `div` 2

bidual ps = sort (map (\(x,y)->(succ y,pred x)) ps)

borrow_bidual = borrow_from bipartite bidual
nbidual = borrow_bidual nat
hbidual = borrow_bidual hypergraph

to_igraph xss= gs where  
  l=genericLength xss
  crosses xs ys = []/=intersect xs ys
  gs=[(fromIntegral i,fromIntegral j)|
     i<-[0..l-1],j<-[i+1..l-1],crosses (xss!!i) (xss!!j)]

to_ngraph n = as nat dag gs where 
  xss=as hypergraph nat n
  gs=to_igraph xss

to_kngraph n 0 = n
to_kngraph n k = to_ngraph (to_kngraph n (k-1))

digraph2dag = map f where f (x,y) = (x,y+x+1)

dag2digraph = map f where f (x,y) | y>x = (x,y-x-1)

dag :: Encoder [N2]
dag = compose (Iso dag2digraph digraph2dag ) digraph

kdag :: N->Encoder [N2]->Encoder [N2]
kdag k t = compose (Iso (dig2dag k) (dag2dig k)) t

dig2dag 0 g = g
dig2dag k g | k>0 = dag2digraph (dig2dag (k-1) g)

dag2dig 0 g = g
dag2dig k g | k>0 = digraph2dag (dag2dig (k-1) g)

dag' :: Encoder [N2]
dag' = compose (Iso dag2digraph digraph2dag ) digraph'

mdag :: Encoder [N2]
mdag = compose (Iso dag2digraph digraph2dag ) mdigraph

binrel2digraph xss=[(fromIntegral x,fromIntegral y)
             |x<-[0..l],y<-[0..l],xss!!x!!y==1] where 
  l=pred (genericLength xss)
  
digraph2binrel []= []  
digraph2binrel ps= msplit (succ l) bs where
  (xs,ys)=unzip ps
  vs=sort (nub (xs++ys))
  l=maximum vs
  is=[0..l]
  f ps xy | xy `elem` ps = 1
  f _ _ = 0
  bs = map (f ps) [(x,y)|x<-is,y<-is]
  msplit _ []  = []
  msplit k xs  = h:(msplit k ts) where (h,ts)=genericSplitAt k xs

binrel :: Encoder [[N]]
binrel = compose (Iso binrel2digraph digraph2binrel ) digraph

keygroup ps = xss where
  qss=groupBy (\p q->fst p==fst q) (sort ps)
  xss=map (\xs->(fst (head xs),map snd xs)) qss

keyungroup xys = [(x,y)|(x,ys)<-xys,y<-ys]  

adigraph :: Encoder [N2]

adigraph = Iso adj2fun fun2adj

fun2adj ls = concat pss where
  lss=map ((as set nat) . succ) ls
  l=genericLength lss
  pss=zipWith f [0..l-1] lss
  f i js=[(i,j)|j<-js]
  
adj2fun rs = ls where
   lss=map snd (keygroup rs)
   ls=map (pred . (as nat set)) lss

ins xs at val = ys where
  fi (hs,ts) = hs ++ (val:ts) 
  ys=fi (genericSplitAt at xs)
 
del xs at = ys where
  fd (hs,(_:ts)) = hs ++ ts 
  ys=fd (genericSplitAt at xs)

subst xs at with = ins (del xs at) at with

gswap ms (i,j) = transp ms (2*i,2*j+1)

transp ms (i,j) = ms' where
  x=ms!!(fromIntegral i)
  y=ms!!(fromIntegral j)
  ms'=subst (subst ms i y) j x

newMem = 0:1:newMem

applyPairs _ [] ms = ms
applyPairs sf (p:ps) ms = applyPairs sf ps (sf ms p)

bitcompute graphType =  (as nat bits) . runPairs . (as graphType nat)

runPairs ps=rs where  
  qs=applyPairs gswap ps newMem 
  rs=genericTake (genericLength ps) qs

encodeTransformer n = pepis_pair (l,as nat dag t) where
  (l,t) = induceTransformer n

induceTransformer n = ((hf l)-(genericLength ps)-1,ps) where
  ps=map f qs
  (l,qs)=induceTransps n
  hf n = n `div` 2
  f (x,y) = (hf (x-1),hf y)
  
induceTransps n = (l,qs) where
   bs= as hff_pars nat n
   l=genericLength bs
   ps=zip [0..l-1] bs
   ls=filter (\(i,b)->(odd i) && (0==b))  ps
   rs=filter (\(i,b)->(even i) && (1==b)) ps
   qs=zipWith f ls rs where
     f (i,_) (j,_) = (i,j)

digraph2transducer = map f where
  f (x,y) = ((x',y'),(bx,by)) where
     ht z=quotRem z 2
     (x',bx)=ht x
     (y',by)=ht y
       
transducer2digraph = map g where
  g ((x',y'),(bx,by))=(x,y) where
    c b z = b+2*z
    x = c bx x'
    y = c by y'

transducer :: Encoder [(N2,N2)]
transducer = compose (Iso transducer2digraph digraph2transducer) digraph

set2sat = map (set2disj . nat2set) where
  shift0 z = if (z<0) then z else z+1
  set2disj = map (shift0. nat2z)
  
sat2set = map (set2nat . disj2set) where
  shiftback0 z = if(z<0) then z else z-1
  disj2set = map (z2nat . shiftback0)

sat :: Encoder [[Z]]
sat = compose (Iso sat2set set2sat) set

toCNF :: [[Z]] -> CNF
toCNF xss = CNF nvars ncls (fromList cls) where
  xs = concat xss
  nvars = toInt (foldl max 0 (map abs xs))
  ncls = length xss
  cls = map toCls xss
  toCls = map (L . toInt)

toInt :: Z->Int
toInt x = fromIntegral x

ssolve :: [[Z]] -> Solution
ssolve xss = s where
  (s,_,_) = solve1 (toCNF xss)

nsolve k  = (xss,s) where
  xss=(as sat nat k)
  s=ssolve xss

isSAT = found . snd . nsolve

isUNSAT = not . isSAT
  
found (Sat _) = True
found (Unsat _) = False

sats xs = [x|x<-xs, isSAT x]

unsats xs = [x|x<-xs, isUNSAT x]

satStats xs = (s,u) where 
  s=genericLength (sats xs)
  u=genericLength (unsats xs)

gmodel2nat (set,m) = pred (fun2nat (m : (set2fun set)))
nat2gmodel n = (fun2set xs,m) where (m:xs) = nat2fun (succ n)

type Gdomain= ([N],N)
gmodel :: Encoder Gdomain
gmodel = compose (Iso gmodel2nat nat2gmodel) nat

dyadic :: Encoder (Ratio N)
dyadic = compose (Iso dyadic2set set2dyadic) set

set2dyadic :: [N] -> Ratio N
set2dyadic ns = rsum (map nexp2 ns) where
  nexp2 0 = 1%2
  nexp2 n = (nexp2 (n-1))*(1%2)

  rsum [] = 0%1
  rsum (x:xs) = x+(rsum xs)

dyadic2set :: Ratio N -> [N]
dyadic2set n | good_dyadic n = dyadic2exps n 0 where
  dyadic2exps 0 _ = []
  dyadic2exps n x = 
    if (d<1) then xs else (x:xs) where
      d = 2*n
      m = if d<1 then d else (pred d)
      xs=dyadic2exps m (succ x)
dyadic2set _ =  
  error  "dyadic2set: argument not a dyadic rational"

good_dyadic kn = (k==0 && n==1) 
  || ((kn>0%1) && (kn<1%1) && (is_exp2 n)) where 
    k=numerator kn
    n=denominator kn

    is_exp2 1 = True
    is_exp2 n | even n = is_exp2 (n `div` 2)
    is_exp2 n = False

dyadic_dist x y = abs (x-y)

dist_for t x y =  as dyadic t 
  (borrow2 (with dyadic t) dyadic_dist x y)
dsucc = borrow (with nat dyadic) succ
dplus = borrow2 (with nat dyadic) (+)

dconcat = lend2 dyadic (++)

pars :: Encoder [Char]
pars = compose (Iso pars2hff hff2pars) hff

pars2hff cs = parse_pars '(' ')' cs

parse_pars l r cs | newcs == [] = t where
  (t,newcs)=pars_expr l r cs

pars_expr l r (c:cs) | c==l = ((H ts),newcs) where 
  (ts,newcs) = pars_list l r cs
     
  pars_list l r (c:cs) | c==r = ([],cs)
  pars_list l r (c:cs) = ((t:ts),cs2) where 
    (t,cs1)=pars_expr l r (c:cs)
    (ts,cs2)=pars_list l r cs1

hff2pars = collect_pars '(' ')'

collect_pars l r (H ns) =
  [l]++ 
    (concatMap (collect_pars l r) ns)
  ++[r] 

to_hill =scanr (\x y->y+(if 0==x then -1 else 1)) 0 

hill t n = to_hill (as t nat n)

bitpars2hff cs = parse_pars 0 1 cs
hff2bitpars = collect_pars 0 1

hff_pars :: Encoder [N]
hff_pars = compose (Iso bitpars2hff hff2bitpars) hff

nat2parnat n = as nat bits (as hff_pars nat n)

parnat2nat n = as nat hff_pars (as bits nat n)

hff_bitsize n= sum (map hff_bsize [0..2^n-1])

hff_bsize k=genericLength (as bits nat (nat2parnat k)) 

info_density_hff n = (n*2^n)%(hff_bitsize n)

pars_hf=Iso bitpars2hff hff2bitpars

hff_pars' :: Encoder [N]
hff_pars' = compose pars_hf hff'

hfs_pars :: Encoder [N]
hfs_pars = compose pars_hf hfs

hfpm_pars :: Encoder [N]
hfpm_pars = compose pars_hf hfpm

hfm_pars :: Encoder [N]
hfm_pars = compose pars_hf hfm

bhfm_pars :: Encoder [N]
bhfm_pars = compose pars_hf hfbm

bhfm_pars' :: Encoder [N]
bhfm_pars' = compose pars_hf hfbm'

hfp_pars :: Encoder [N]
hfp_pars = compose pars_hf hfp

parsize_as t n = genericLength (hff2bitpars (as t nat n))

parsizes_as t m = map (parsize_as t) [0..2^m-1]
 
nat2hfsnat n = as nat bits (as hfs_pars nat n)

hfs_bitsize n= sum (map hfs_bsize [0..2^n-1])

hfs_bsize k=genericLength (as bits nat (nat2hfsnat k)) 
  
info_density_hfs n = (n*2^n)%(hfs_bitsize n)

kraft t n=sum xs where
  f x = 1/2^x
  xs=map (f . (parsize_as t)) [0..n-1]
  
kraft_check t n = kraft t n <=1  

to_elias :: N -> [N]
to_elias n = (to_eliasx (succ n))++[0]

to_eliasx 1 = []
to_eliasx n = xs where
  bs=to_lbits n
  l=(genericLength bs)-1
  xs = if l<2 then bs else (to_eliasx l)++bs

from_elias :: [N] -> (N, [N])
from_elias bs = (pred n,cs) where (n,cs)=from_eliasx 1 bs

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

kraft_elias n = sum (map f [0..n-1]) where 
  f k=1/2^(genericLength (as elias nat k))

kraft_encoding t n = sum (map f [0..n-1]) where 
  f k=1/2^(genericLength (as t nat k))

after2 i j t = compose (Iso i j) t
after i t = after2 i i t

natInvert = borrow_from perm invertPerm nat

natDual = borrow_from bits dual nat

auto t s = (as nat s) . (as t nat) 

autoS = auto fun fun'

autoS' = auto fun' fun

autoP = auto mset pmset

autoP' = auto pmset mset

autoH = auto hff hff'

autoH'= auto hff' hff

autoM = auto hfm hfpm

autoM' = auto hfpm hfm

autoLess t s m = filter (\i->auto t s i<i) [0..2^m-1] 

pencode = pcode id
pdecode = pcode invertPerm

pcode f k n = n' where
  ps=as perm nat k
  ps'=f ps
  l=genericLength ps'
  ns=to_tuple l n
  ns'=applyPerm ps' ns
  n'=from_tuple ns'
  
applyPerm ps xs = [xs!!(fromIntegral p)|p<-ps]

invertPerm ps = snd (unzip (sort (zip ps [0..])))

pencode' = pcode' id
pdecode' = pcode' invertPerm

pcode' f k n = n' where
  ps=as perm nat k
  ps'=f ps
  l=genericLength ps'
  ns=to_tuple l (as gray nat n)
  ns'=applyPerm ps' ns
  n'=as nat gray (from_tuple ns')

pencode'' k n = (as gray fun') (map (pencode' k) (as fun' gray n))
pdecode'' k n = (as gray fun') (map (pdecode' k) (as fun' gray n))

grayPerm n = p where 
  ps=map (as gray nat) [0..2^n-1]
  p=as nat perm ps

ghff :: Encoder T
ghff = compose (hylo gray) gray

gray2fun = nat2fun . gray2nat
fun2gray = nat2gray . fun2nat 

gray_fun = Iso gray2fun fun2gray

ghff' :: Encoder T
ghff' = compose (hylo gray_fun) gray

gray2set = nat2set . gray2nat
set2gray = nat2gray . set2nat 

gray_set = Iso gray2set set2gray

ghfs :: Encoder T
ghfs = compose (hylo gray_set) gray

parmorph = as nat pars . dualpars . as pars nat

dualpars  = flip_pars '(' ')' . reverse

flip_pars _ _ [] = []
flip_pars l r (x:xs) | x==l = r: (flip_pars l r xs)
flip_pars l r (x:xs) | x==r = l: (flip_pars l r xs)

pkencode auto passkey plaintext = cyphertext where
  k=as nat string passkey
  p=as nat string plaintext
  c=auto k p
  cyphertext=as string nat c

simpleEncode k p = k `xor` (as gray nat p)
simpleDecode k q = as nat gray (k `xor` q)

data Base = Adenine | Cytosine | Guanine | Thymine 
  deriving(Eq,Ord,Show,Read)

type DNA = [Base]

alphabet2code Adenine = 0
alphabet2code Cytosine = 1
alphabet2code Guanine = 2 
alphabet2code Thymine = 3

code2alphabet 0 = Adenine
code2alphabet 1 = Cytosine
code2alphabet 2 = Guanine 
code2alphabet 3 = Thymine

dna2nat  = (from_base 4) . (map alphabet2code)

nat2dna = (map code2alphabet) . (to_base 4)

dna :: Encoder DNA
dna = compose (Iso dna2nat nat2dna)  nat

dna_complement :: DNA -> DNA
dna_complement = map to_compl where
  to_compl Adenine = Thymine
  to_compl Cytosine = Guanine
  to_compl Guanine = Cytosine
  to_compl Thymine = Adenine

dna_reverse :: DNA -> DNA
dna_reverse = reverse

dna_comprev :: DNA -> DNA
dna_comprev = dna_complement . dna_reverse

data Polarity =  P3x5 | P5x3 
  deriving(Eq,Ord,Show,Read)

data DNAstrand = DNAstrand Polarity DNA 
  deriving(Eq,Ord,Show,Read)

strand2nat (DNAstrand polarity strand) = 
  add_polarity polarity (dna2nat strand) where 
    add_polarity P3x5 x = 2*x
    add_polarity P5x3 x = 2*x-1
    
nat2strand n =
  if even n 
     then DNAstrand P3x5 (nat2dna (n `div` 2))
     else DNAstrand P5x3 (nat2dna ((n+1) `div` 2))

dnaStrand :: Encoder DNAstrand
dnaStrand = compose (Iso strand2nat nat2strand) nat

dna_down :: DNA -> DNAstrand
dna_down = (DNAstrand P3x5) . dna_complement

dna_up :: DNA -> DNAstrand
dna_up = DNAstrand P5x3

data DoubleHelix = DoubleHelix DNAstrand DNAstrand
   deriving(Eq,Ord,Show,Read)

dna_double_helix :: DNA -> DoubleHelix
dna_double_helix s = 
  DoubleHelix (dna_up s) (dna_down s)

rannat = rand (2^50)

rand :: N->N->N
rand max seed = n where 
  (n,g)=randomR (0,max) (mkStdGen (fromIntegral seed))   

rantest :: Encoder t->Bool
rantest t = and (map (rantest1 t) [0..255])

rantest1 t n = x==(visit_as t x) where  x=rannat n

visit_as t = (to nat) . (from t) . (to t) . (from nat) 

isotest = and (map rt [0..25])

rt 0 = rantest nat
rt 1 = rantest fun
rt 2 = rantest set
rt 3 = rantest bits
rt 4 = rantest funbits
rt 5 = rantest hfs
rt 6 = rantest hff
rt 7 = rantest uhfs
rt 8 = rantest uhff
rt 9 = rantest perm
rt 10 = rantest hfp
rt 11 = rantest nat2
rt 12 = rantest set2
rt 13 = rantest clist
rt 14 = rantest pbdd
rt 15 = rantest bdd
rt 16 = rantest rbdd
rt 17 = rantest digraph
rt 18 = rantest graph
rt 19 = rantest mdigraph
rt 20 = rantest mgraph
rt 21 = rantest hypergraph
rt 22 = rantest dyadic
rt 23 = rantest string
rt 24 = rantest pars
rt 25 = rantest dna

nth thing = as thing nat
nths thing = map (nth thing)
stream_of thing = nths thing [0..]

ran thing seed largest = head (random_gen thing seed largest 1)

random_gen thing seed largest n = genericTake n
  (nths thing (rans seed largest))
  
rans seed largest = 
    randomRs (0,largest) (mkStdGen seed)

length_as t = fit genericLength (with nat t)
sum_as t = fit sum (with nat t)
size_as t = fit tsize (with nat t)

nat2self f n = (to_elias l) ++ concatMap to_elias ns where
  ns = f n
  l=genericLength ns
  
nat2sfun n = nat2self (as fun nat) n   

self2nat g ts = (g xs,ts') where 
  (l,ns) = from_elias ts
  (xs,ts')=take_from_elias l ns

  take_from_elias 0 ns = ([],ns) 
  take_from_elias k ns = ((x:xs),ns'') where
     (x,ns')=from_elias ns
     (xs,ns'')=take_from_elias (k-1) ns'
  
sfun2nat ns = xs where
  (xs,[])=self2nat (as nat fun) ns

sfun :: Encoder [N]
sfun = compose (Iso sfun2nat nat2sfun) nat

linear_sparseness_pair t n = 
  (genericLength (to_elias n),genericLength (nat2self (as t nat) n))

linear_sparseness f n = x/y where (x,y)=linear_sparseness_pair f n 

sparseness_pair f n = 
  (genericLength (to_elias n),genericLength (as f nat n))

sparseness f n = x/y where (x,y)=sparseness_pair f n 

sparses_to m = [n|n<-[0..m-1],
  (genericLength (as hff_pars nat n)) 
  <
  (genericLength (as elias nat n))]

ppair pairingf (p1,p2) | is_prime p1 && is_prime p2 = 
  from_pos_in ps (pairingf (to_pos_in ps p1,to_pos_in ps p2)) where 
    ps = primes
 
punpair unpairingf p | is_prime p = (from_pos_in ps n1,from_pos_in ps n2) where 
  ps=primes
  (n1,n2)=unpairingf (to_pos_in ps p)

hyper_primes u = [n|n<-primes, all_are_primes (uparts u n)] where
  all_are_primes ns = and (map is_prime ns)
  
uparts u = sort . nub . tail . (split_with u) where
    split_with _ 0 = []
    split_with _ 1 = []
    split_with u n = n:(split_with u n0)++(split_with u n1) where
      (n0,n1)=u n  

strange_sort = (from nat_set) . (to nat_set)

strange_sort' = (to mset) . (from mset)
strange_sort'' = (as mset nat) . (as nat mset)

pcompose (s1,t1) (s2,t2) | t1==s2 = (s1,t2)
pcompose _ _ = error "pcompose: bad morphisms"

is_pcomposable (s1,t1) (s2,t2) | t1==s2 = True
is_pcomposable _ _ = False

ncompose n m1 m2 = as nat nat2 m where 
  c=as mdigraph nat n
  m=pcompose (c!!m1) (c!!m2)

rtrans ps = (ids ps) ++ (trans ps)

trans ps = sort $ nub $ trans2 ps where

  trans1 ps = nub [q|q<-qs,not (is_id q)] where
     is_id (x,y) = x==y 
     qs=ps++[pcompose p q|p<-ps,q<-ps,is_pcomposable p q]

  trans2 ps = if (l==l1) then ps else (trans2 ps1) where
    l=genericLength ps 
    ps1=trans1 ps
    l1=genericLength ps1

to_trans n = trans $ as digraph nat n

ntrans n = as nat digraph $ to_trans n

vertset ps = sort $ nub [z|(x,y)<-ps,z<-[x,y]]

ids ps = [(x,x)|x<-vertset ps]

pairs2graph ps = l where
  l=genericLength ps
  
gtest = map f (vertices x) where 
  (x,f,z)=graphFromEdges [(0,10,[10,20]),(1,10,[20]),(2,20,[10])]
  

bitcount n = head [x|x<-[1..],(2^x)>n]
max_bitcount ns = foldl max 0 (map bitcount ns)

to_maxbits maxbits n = 
  bs ++ (genericTake (maxbits-l)) (repeat 0) where 
    bs=to_base 2 n
    l=genericLength bs

primes = 2 : filter is_prime [3,5..]

is_prime p = [p]==to_primes p

to_primes n | n>1 = to_factors n p ps where 
  (p:ps) = primes

to_factors n p ps | p*p > n = [n]
to_factors n p ps | 0==n `mod` p = p : to_factors (n `div` p)  p ps 
to_factors n p ps@(hd:tl) = to_factors n hd tl

msetInter xs ys = sort (msetInter' xs ys)

msetInter' [] _ = []
msetInter' _ [] = []
msetInter' (x:xs) (y:ys) | x==y = 
  (x:zs) where zs=msetInter' xs ys
msetInter' (x:xs) (y:ys) | x<y = msetInter' xs (y:ys)
msetInter' (x:xs) (y:ys) | x>y = msetInter' (x:xs) ys

msetDif xs ys = sort (msetDif' xs ys)

msetDif' [] _ = []
msetDif' xs [] = xs
msetDif' (x:xs) (y:ys) | x==y = zs where 
  zs=msetDif' xs ys
msetDif' (x:xs) (y:ys) | x<y = (x:zs) where 
  zs=msetDif' xs (y:ys)
msetDif' (x:xs) (y:ys) | x>y = zs where 
  zs=msetDif' (x:xs) ys

msetSymDif xs ys = 
  sort ((msetDif xs ys) ++ (msetDif ys xs))

msetUnion xs ys = sort ((msetDif xs ys) ++ 
  (msetInter xs ys) ++ (msetDif ys xs))
  
msetIncl xs ys = xs==msetInter xs ys
 

fun2g ns = nat2fgs nat2fun ns
set2g ns = nat2sgs nat2set ns
perm2g ns = nat2fgs nat2perm ns
pmset2g ns = nat2fgs nat2pmset ns
bmset2g ns = nat2fgs nat2bmset ns

nat2fg f n = nat2gx fun_edge f nat2pftree n :: Gr N Int

nat2fgs f ns = nat2gsx fun_edge f nat2pftree ns :: Gr N Int

nat2sg f n = nat2gx set_edge f nat2pftree n :: Gr N ()

nat2sgs f ns = nat2gsx set_edge f nat2pftree ns :: Gr N ()

set_edge xs (a,b,i) = (lookUp a xs,lookUp b xs,())

fun_edge xs (a,b,i) = (lookUp a xs,lookUp b xs,i)

nat2gx e f g n = mkGraph vs  (map (e xs) es) where 
  es=g f n
  (xs,vs)=labeledVertices es

nat2gsx e f g ns = mkGraph vs  (map (e xs) es)  where 
  es=nub (concatMap (g f) ns)
  (xs,vs)=labeledVertices es
  
labeledVertices es= (xs,vs) where  
  xs=fvertices es
  is=[0..(length xs)-1]
  vs = zip is xs
     
nat2pftree f n = nub (nat2pftreex f (n,n,0))

nat2pftreex f (_,n,_) = ps ++ (concatMap (nat2pftreex f) ps) where
  ps = nat2pfun f (n,n,0)

nat2pfun _ (_,0,_) = []
nat2pfun f (_,n,_) | n> 0 = ps where 
  ps = zipWith (\x i->(n,x,i)) (f n) [0..]

fvertices ps = (sort . nub) (concatMap f ps) where
  f (a,b,_) = [a,b]

lookUp n ns = i where Just i=elemIndex n ns

edges2gr ::  [(N,N)] -> Gr Int ()

edges2gr es = mkGraph lvs les where 
  vs=[0..foldl max 0 (concatMap g es)]
  lvs=zip vs vs
  les=map f es
  f (x,y) = (fromIntegral x,fromIntegral y,())
  g (x,y) = [fromIntegral x,fromIntegral y]

pairs2gr ::  [(N,N)] -> Gr N ()

pairs2gr ps = mkGraph lvs les where 
  vs=to_vertices ps
  lvs=zip [0..] vs
  es=to_edges vs ps
  les=map f es
  f (x,y) = (x,y,())

to_vertices es = sort $ nub $ concat [[fst p,snd p]|p<-es]

to_edges vs ps = map (f vs) ps where
  f vs (x,y) = (lookUp x vs,lookUp y vs)

unpairing_edges f tt = nub  (h f tt) where
  h _ tt | tt<2 = []
  h f n  = ys where
     (n0,n1)=f n
     ys= (n,n0,0):(n,n1,1):
           (h f n0) ++ 
           (h f n1)

untupling_edges f k l tt = nub  (h f k tt) where
  h _ _ tt | tt<l = []
  h f k n  = ys where
     ns = f k n
     ys = (zip3 (repeat n) ns [0..]) ++
          (concatMap (h f k) ns) 
  

nat2edges k n = xs ++ (concatMap (expandEdge k) xs) where 
  p2e (c,e) = (n,e,c)
  xs= map p2e (nat2kpoly k n)

expandEdge k (_,e,_) | e < k = []
expandEdge k (_,e,_) = nat2edges k e

to_unpair_graph f tt = nat2fun_graph (unpairing_edges f) tt

to_untuple_graph f k l tt = nat2fun_graph (untupling_edges f k l) tt

nat2fun_graph f n = nat2graph f n :: Gr N Int

to_hb_graph k n = nat2hb_graph (nat2edges k) n

nat2hb_graph f n = nat2graph f n :: Gr N N

nat2graph f n = mkGraph vs fs where
  es=f n
  (xs,vs)=labeledVertices es
  fs=map (fun_edge xs) es

gviz g = writeFile "iso.gv" 
  ((graphviz g "" (0.0,0.0) (2,2) Portrait)++"\n")

funviz f n = gviz (nat2fg f n)  

setviz f n = gviz (nat2sg f n)

eviz t n = gviz (edges2gr (as t nat n)) -- dag, digraph

pviz t n = gviz (pairs2gr (as t nat n))

psviz ps = gviz (pairs2gr ps)

uviz f tt = gviz (to_unpair_graph f tt) -- unpairings

tviz f k tt = gviz (to_untuple_graph f k 2 tt)

pbviz k tt = gviz (to_untuple_graph to_sqbase k k tt)

v3x1 k tt = gviz (to_untuple_graph to_3x1 k k tt)

hbviz k n = gviz (to_hb_graph k n)

fviz t n = gviz (es2g (as t nat n))

es2g :: [(N, N)] -> Gr () Int

es2g es = mkGraph lvs les where (lvs,les)=es2ls es

es2ls es = (lvs,les) where
  es' = map (\(x,y)->(fromIntegral x,fromIntegral y)) es
  g ((x,y),l)=(x,y,l)
  les=map g (zip es' [0..length es-1]) 
  vs = [0..foldr max 0 (concatMap f es')]
  lvs=map (\x->(x,())) vs
  f (from,to)=[from,to]

plot3d f xs ys = plotFunc3d [Title ""] [] xs ys f

plotop op m= plot3d op xs xs where xs=[0..2^m-1]

cplot3d f = plot3d (curry f)

pair3d pf m | m<=8 = cplot3d pf ls ls where ls=[0..2^m-1]

plotpairs m | m<=2^8 = cplot3d bitpair ls ls where ls=[0..m-1]

plotdyadics m = plotList 
  [Title "Dyadics"] 
  (map (fromRational . (as dyadic nat)) [0..m-1])

plotkraft t m = plotList 
  [Title "Kraft function"] 
  (map (kraft t) [0..2^m-1])
  
plotelias m = plotList 
  [Title "Elias encoding length"] 
  (map kraft_elias [0..2^m-1])
    
sizes_to m t = map (size_as t) [0..m-1]

plot_hf m = plotLists [Title "Bit, BDD, HFF, HFS, and HFP sizes"] 
  ( 
    [bits_to m,bsizes_to m] ++ 
    (map (sizes_to m) [hff,hfs,hfm,hfp])
  )

plot_hf1 m = plotLists [Title "Bit, HFF, HFS, HFM and HFP sizes"] 
  ( 
    [bits_to m] ++ 
    (map (sizes_to m) [hff,hfs,hfm,hfp])
  )
  
plot_good m = plotLists [Title "Bit and HFF sizes"] 
  ( 
    [bits_to m] ++ 
    (map (sizes_to m) [hff])
  )
  
plot_best m = plotLists [Title "Bit, BDD and HFF and HFF' sizes"] 
  ( 
    [bits_to m,bsizes_to m] ++ 
    (map (sizes_to m) [hff,hff'])
  )

plot_worse m = plotLists [Title "HFM, HFS and HFP sizes"] 
  ( 
    (map (sizes_to m) [hfm,hfs,hfp])
  )

plot_hfs_hfp m = plotLists [Title "HFS and HFP sizes"] 
  ( 
    (map (sizes_to m) [hfs,hfp])
  )
  
plot hf m = plotx [hf] m

plotx hfx m = plotLists [Title "HF tree size"] 
  ( 
    (map (sizes_to (2^m-1)) hfx)
  )

-- plots pairs
pplot f m = plotPath [] (map (to_ints . f) [0..2^m-1]) 

priplot f m = plotPath [] (map (to_ints . f) (genericTake m primes))

zplot f m = plotPath [] (map (to_ints . f) [-(2^m)..2^m-1]) 

to_ints (i,j)=(fromIntegral i,fromIntegral j)

diplot n = plotPath [] (map to_ints (as digraph nat n))

bsize_of n = robdd_size (as rbdd nat n)

bsizes_to m = map bsize_of [0..m-1]

bits_to m = map s [0..m-1] where s n = genericLength (as bits nat n)

plot_linear_sparseness m = plotLists [Title "Linear Sparseness"] 
  [(map (linear_sparseness fun) [0..m-1]),
   (map (linear_sparseness pmset) [0..m-1]),
   (map (linear_sparseness mset) [0..m-1]),
   (map (linear_sparseness set) [0..m-1]),
   (map (linear_sparseness perm) [0..m-1])]


plot_sparseness m = plotLists [Title "Recursive Sparseness"] 
  [(map (sparseness hff_pars) [0..m-1]),
   (map (sparseness hfpm_pars) [0..m-1]),
   (map (sparseness hfm_pars) [0..m-1]),
   (map (sparseness hfs_pars) [0..m-1]),
   (map (sparseness hfp_pars) [0..m-1])]

plot_sparseness1 m = plotLists 
  [Title "Recursive Sequence vs. Multiset Sparseness"] 
  [
   (map (sparseness hff_pars) [0..m-1]),
   (map (sparseness hfpm_pars) [0..m-1])
  ]
  
plot_sparseness2 m = plotLists [Title "Recursive Multiset Sparseness"] 
  [
   (map (sparseness bhfm_pars) [0..m-1]),
   (map (sparseness hfm_pars) [0..m-1])
  ]

plot_sparseness3 m = plotLists [Title "Recursive Multiset Sparseness"] 
  [
   (map (sparseness hff_pars) [0..m-1]),
   (map (sparseness hff_pars') [0..m-1])
  ]


plot_sparseness4 m = plotLists 
  [Title "Recursive Multiset vs Multiset with Primes Sparseness"] [
   (map (sparseness hfm_pars) [0..m-1]),
   (map (sparseness hfpm_pars) [0..m-1])
  ]

plot_sparseness5 m = plotLists 
  [Title "Recursive Multisets vs. Sequences"] [
   (map (sparseness hff_pars) [0..m-1]),
   (map (sparseness hfm_pars) [0..m-1])
  ]
        
plot_selfdels m = plotLists 
   [Title "Self-delimiting codes: Undelimited vs. Elias vs. HFF"] 
   [(map (genericLength . (as bits nat)) [0..m-1]),
    (map (genericLength . (as elias nat)) [0..m-1]),
    (map (genericLength . (as hff_pars nat)) [0..m-1])]

plot_pairs_prods unpF m = plotLists [Title "Pairs vs. products"]  
   [ms,prods] where
     ms=[1..m]
     pairs=map unpF ms
     prods=map prod pairs where prod (x,y)=2*x*y
 
plot_lifted_pairs m = 
   plotLists [Title "Lifted pairs"]  [us0,us1] where 
     ms=[0..m-1]
     pairs=map bitunpair ms
     us0=map fst pairs
     us1=map snd pairs
     
plot_lifted_pairs1 m = 
   plotLists [Title "Lifted pairs and products"]  [ps,s0,s1,xys] where 
     ms=[0..m-1]
     pairs=map bitunpair ms
     us0=map fst pairs
     us1=map snd pairs
     ps=zipWith (*) us0 us1
     s0=map (^2) us0
     s1=map (^2) us1
     xys=map f pairs where
       f (x,y) = x*y
 
plot_primes_prods m = plotLists [Title "Primes vs. products"]  
  [ps,prods] where 
     ms=[0..m]
     ps=genericTake m primes
     pairs=map bitunpair ps
     prods=map prod pairs where prod (x,y)=2*x*y     
   
plot_hypers_prods m = plotLists [Title "Hyper-primes vs. products"]
   [ps,prods] where 
     ms=[0..m]
     ps=genericTake m (hyper_primes bitunpair)
     pairs=map bitunpair ps
     prods=map prod pairs where prod (x,y)=2*x*y  

hset n=gviz  (nat2sg nat2set n)
hfun n=gviz (nat2fg nat2fun n)

hmset n=gviz (nat2fg nat2mset n)
hperm n=gviz (nat2fg nat2perm n)
dig n =pviz digraph n
dig' n =pviz digraph' n
plotdag n = pviz dag n

hset' n=gviz  (nat2sg nat2set' n)
hfun' n=gviz (nat2fg nat2ftuple n)
hmset' n=gviz (nat2fg nat2mset' n)
hpset' n=gviz (nat2sg ((as set mset) . nat2pmset) n)

unp' tt= uviz unpair' tt
unpp' n=pplot unpair' n
unpp n=pplot bitunpair n

---cunp tt= uviz cunpair tt
cunpp n=pplot cunpair n

plotcantor n =pplot cantor_unpair n

p3d' m = pair3d pair' m 

p3d pf m = pair3d pf m 

ukl k l n = uviz (unpairKL k l) n

uklp k l n = pplot (unpairKL k l) n

klp k l m = pair3d (pairKL k l) m

f4=gviz (nat2fg nat2perm 2009)

f6=plotpairs 64
f7=plotdyadics 256

f8=plot_best (2^6)
f8a=plot_good (2^10)

f9=plot_worse (2^10)
f9a=plot_hfs_hfp (2^16)
f9b=plot_hfs_hfp (2^17)
f10=plot_hf (2^8)
f10a=plot_hf1 (2^8)

f11a=plot_linear_sparseness (2^7)
f11=plot_sparseness (2^8)
f11b=plot_sparseness1 (2^8)
f11c=plot_sparseness2 (2^10)

f12=plot_sparseness (2^14)

f13=plot_sparseness (2^17)

f14=plot_selfdels (2^7)

fs1 m=plotLists 
  [Title "Representation Sizes"] 
  [bs,es,hffs,hfms,hfss,hfps] where 
       bsize n=genericLength (as bits nat n)
       bs=map bsize [0..2^m-1]
       esize n=genericLength (as elias nat n)
       es=map esize [0..2^m-1]      
       hffs=parsizes_as hff m
       hfms=parsizes_as hfm m
       hfss=parsizes_as hfs m
       hfps=parsizes_as hfp m

fs1a m=plotLists 
  [Title "Representation Sizes"] 
  [bs,es,hffs] where 
       bsize n=genericLength (as bits nat n)
       bs=map bsize [0..2^m-1]
       esize n=genericLength (as elias nat n)
       es=map esize [0..2^m-1]
       hffs=parsizes_as hff m
 
fs1b m=plotLists 
  [Title "Representation Sizes"] 
  [hfms,hfss,hfps] where 
       hfms=parsizes_as hfm m
       hfss=parsizes_as hfs m
       hfps=parsizes_as hfp m

             
f15=plotList [] (sparses_to (2^18))

dip m = plotf di m

dup m = plotf ndual m

-- see also plot3d f m
plotf f m = plotList [] (map f [0..2^m-1])
plotf1 f k m = plotList [] (map f [2^k..2^m-1])

penc0 = plotf (pencode 12239) 8

plotss xss = plotFunc3d [] [] ks ys f where
  ks=[0..length xss-1]
  ls=map length xss
  len=foldl max 0 ls
  ys=[0..len-1]
  zss= map (\xs->take len (xs++repeat 0)) xss
  f x y =   (zss!!(fromIntegral x))!!(fromIntegral y)


f16=gviz (nat2fgs nat2fun [0..7])

arp24 i =468395662504823 + 205619*23*i

arps24 = map arp24 [0..23]

arp25 i = 6171054912832631 + 366384*23*i

arps25 = map arp25 [0..24]

f17 = gviz (fun2g arps24)
f17a = gviz (fun2g arps25)

f18 = gviz (fun2g [2^65+1,2^131+3])

f18a = gviz (set2g [2^65+1,2^131+3])


f19 = gviz (fun2g [0..7])

f20 = gviz (pmset2g [0..7])

f20a = gviz (bmset2g [0..7])

f21 = gviz (set2g [0..7])

f22 = gviz (perm2g [0..7])

isoigraph n = psviz (to_igraph (as hypergraph nat n))
isobi n = psviz (as bipartite nat n)

g1 tt= uviz bitunpair tt
g2 tt= uviz pepis_unpair tt
g2' tt= uviz pepis_unpair' tt
g3 tt= uviz rpepis_unpair tt

ug1 tt = uviz (altunpair bitunpair) tt
ug2 tt = uviz (altunpair pepis_unpair) tt

up1 n=pplot (altunpair bitunpair) n
up2 n=pplot (altunpair pepis_unpair) n


isofermat=uviz mset_unpair 65537
isofermat1=uviz mset_unpair 142781101
isonfermat=uviz mset_unpair 34897
mhyper n=uviz mset_unpair (2^n+1)
punpairs n=uviz mset_unpair (2^n+1)


prifraq n=priplot (punpair bitunpair) n -- 1000

isopairs = plot_pairs_prods bitunpair 256
misopairs = plot_pairs_prods mset_unpair 256

isoprimes = plot_primes_prods 256
isohypers = plot_hypers_prods 256

ip1 n=pplot bitunpair n
ip2 n=pplot pepis_unpair n
isounpair3=pplot mset_unpair 10
isounpair4=pplot xorunpair 10
isoyunpair n =pplot yunpair n

isozunpair n=zplot zunpair n
isorepair i1 i2 m = plotList [] (map (repair i1 i2) [0..2^m-1])

isobij f m = plotList [] (map f [0..2^m-1])

-- xorbij is the diff between id and f 
isoxbij f m = plotList [] (map g [0..2^m-1]) where g=xorbij f

-- bijection N->N using multisets and factorings
ms2pms n = as nat pmset (as mset nat n)

pms2ms n = as nat mset (as pmset nat n)

-- same but iterating k times
kms2pms 0 n = n
kms2pms k n = ms2pms (kms2pms (k-1) n) 

kpms2ms 0 n = n
kpms2ms k n = pms2ms (kpms2ms (k-1) n) 

lms k m = [x|x<-[0..2^m-1], kms2pms k x < kpms2ms k x]

xms k m = [x|x<-[0..2^m-1],kms2pms k x < x]

eqms k m = [x|x<-[0..2^m-1],kms2pms k x == x]

xpms k m = [x|x<-[0..2^m-1],kpms2ms k x < x]

eqpms k m = [x|x<-[0..2^m-1],kpms2ms k x == x]

qms k m = 
 [(toRational (kpms2ms k x)) - (toRational (kms2pms k x))|x<-[1..2^m-1]]

q1 k m = plotList []  (qms k m)

q2 k m = plotLists []  
  [map (kms2pms k) xs,map (kpms2ms k) xs] where 
    xs = [0..2^m-1]

mult_vs_pairing p1 p2 = fromRational ( (p1*p2) % (ppair bitpair (p1,p2)))
mult_vs_mset_pairing p1 p2 = fromRational ((p1*p2) % (ppair mset_pair (p1,p2)))


q3 n = plotFunc3d 
        [Title "Prime Multiplication vs. Prime Pairing"] [] 
          ps ps  mult_vs_pairing where
            ps=genericTake n primes

q4 n = plotFunc3d 
  [Title "Prime Multiplication vs. Prime Multiset Pairing"] [] 
        ps ps mult_vs_mset_pairing where
        ps=genericTake n primes
       
n4a n = plotFunc3d [Title "Multiplication"] [] 
        ps ps (*) where
          ps=[0..2^n-1]

n4b n = plotFunc3d [Title "Multiset Pairing"] [] 
        ps ps (curry mset_pair) where
          ps=[0..2^n-1]


n4c n = plotFunc3d [Title "mprod operation"] [] 
        ps ps (mprod) where
          ps=[0..2^n-1]

n4d n = plotFunc3d [Title "pmprod' operation"] [] 
        ps ps (pmprod') where
          ps=[0..2^n-1]

n4e n = plotFunc3d [Title "mprod' operation"] [] 
        ps ps (mprod') where
          ps=[0..2^n-1]


n4f n = plotFunc3d [Title "mprod' x y/ x * y"] [] 
        ps ps (\x y->fromRational ((mprod' x y) % (x*y))) where
          ps=[1..2^n]

mplot f ps = plotFunc3d [Title "product operation"] [] ps ps f
 
dplot f g ps = plotFunc3d [Title "division comparison of operations"] [] 
        ps ps (\x y->fromRational ((f x y) % (g x y))) where

nplot f n = mplot f [1..2^n] 
rplot f n = mplot f (genericTake n primes)

ndplot f g n = dplot f g [1..2^n] 
rdplot f g n = dplot f g  (genericTake n primes)
                    
expMexp k m = plotLists []  
   [map (\x->x^k) xs, map (\x->mexp' x k) xs] where 
   xs = [0..2^m]
    
p4a n = plotFunc3d [Title "Prime Multiplication"] [] 
        ps ps (*) where
          ps=genericTake n primes

p4b n = plotFunc3d [Title "Prime Multiset Pairing"] [] 
        xs ys (curry mset_pair) where
        ps=genericTake n primes
        xs=ps
        ys=ps

p4c n = plotFunc3d [Title "mprod on primes"] [] 
        xs ys (mprod) where
        ps=genericTake n primes
        xs=ps
        ys=ps

p4d n = plotFunc3d [Title "pmprod on primes"] [] 
        xs ys (pmprod) where
        ps=genericTake n primes
        xs=ps
        ys=ps
 
 
p4f n = plotFunc3d [Title "mprod' x y/ x * y"] [] 
        ps ps (\x y->(mprod' x y) % (x*y)) where
          ps=genericTake n primes
                         
q4c n = plotFunc3d [Title "Prime Pairing"] [] 
        ps ps (curry bitpair) where
          ps=genericTake n primes
                
q5 n = plotLists 
  [Title "Prime Multiplication vs. Prime Pairing curves"] 
  [prods,pairs] where 
    us= map bitunpair [0..2^n-1]
    (xs,ys) = unzip us  
    ps=primes
    xs'=map (from_pos_in ps) xs
    ys'=map (from_pos_in ps) ys
    prods = zipWith (*) xs' ys'
    us'=zip xs' ys'
    pairs= map (ppair mset_pair) us'

plot_gauss_op f m = plotFunc3d title [] zs zs (curry f) where
  title=[Title "Gauss Integer operations through Pairing Functions"]
  zs=[-2^m..2^m-1]

gsum m = plot_gauss_op gauss_sum m
gdif m = plot_gauss_op gauss_dif m

gprod m = plot_gauss_op gauss_prod m

compose_nperm l nf nx = ps where
   fs=nth2perm (l,nf)
   xs=nth2perm (l,nx)
   ys=applyPerm fs xs
   (_,ps)=perm2nth ys

ip n = as nat perm cs where
  bs=as perm nat n
  cs=invertPerm bs

rp n = as nat perm cs where
  bs=as perm nat n
  cs=reverse bs
 
ipb = ip . ib
ibp = ib . ip
  
--permPow l p k = 

-- complement borrowed from bits
ib n = as nat bits cs where
  bs=as bits nat n
  cs=invertBits bs

-- complement in {0,1}^*  
invertBits bs = map (\x->if 0==x then 1 else 0) bs
  
pc1 l = plotFunc3d [Title "Product as permutations"] 
  [] ns ns (\x y->compose_nperm l (fromIntegral x) (fromIntegral y)) where 
    lim=product [1..l] 
    ns=[0..lim-1]


-- nat to nat bijections
pflip u p n = p (y,x) where (x,y) = u n
 
pf = pflip pepis_unpair pepis_pair
bf = pflip bitunpair bitpair
      
xorunpair n = (x `xor` y,y) where (x,y)=bitunpair n

xorpair (x,y) = bitpair (x `xor` y,y)

yunpair n = (x `xor` y,y) where (x,y)=pepis_unpair' n

ypair (x,y) = pepis_pair' (x `xor` y,y)

xb = bitpair . xorunpair

nr = (as nat fun) . (fit reverse nat)

di n = as nat digraph (map rev ps) where 
  ps=as digraph nat n
  rev (x,y)=(y,x)

xorbij f n = n `xor` (f n)

enctest w = isoDecode bs pwd (isoEncode bs pwd w) where 
  pwd="eureka"
  bs=bijlist

isoDecode bs pwd txt =  encodeWith bs reverse pwd txt

isoEncode bs pwd txt = encodeWith bs id pwd txt

bijlist = [di,bf,ip,xb,ib,rp,nr,(xbij 2 3),(xbij 3 4)]

encodeWith bs r pwd txt = as string nat ctxt where 
  ntxt = as nat string txt
  npwd = as nat string pwd
  b x = npwd `xor` x
  ctxt = foldr (.) id (r (pwd2bs npwd (b:bs))) ntxt

pwd2bs npwd bs = newbs where
  l=genericLength bs
  lfact=product [1..l]
  mpwd=npwd `mod` lfact
  wperm = nth2perm (l,mpwd)
  newbs=applyPerm wperm bs

combWith f xs ys = [f x y|x<-xs,y<-ys] 

comb f m = sort (combWith f xs xs) where xs=[0..2^m-1]


     
-- tests

refl1 x=
  as nat set $
  as set fun $
  as fun funbits $
  as funbits pbdd $
  as pbdd hfs $
  as hfs hff $
  as hff uhfs $
  as uhfs bits $
  as bits bdd $ 
  as bdd nat x

refl2 x=
  as nat bdd $
  as bdd bits $ 
  as bits uhfs $
  as uhfs hff $
  as hff hfs $
  as hfs pbdd $
  as pbdd funbits $
  as funbits fun $
  as fun set $
  as set nat x


cross = bitpair . cross2 . bitunpair

cross2 (a,b) = (ab,ba) where
  (a1,a2)  = bitunpair a
  (b1,b2) = bitunpair b
  ab = bitpair (a1,b2)
  ba = bitpair (b1,a2)

repair iso1 iso2 n =
  as nat iso2 (as iso1 nat n)

rep1 = repair nat2 pnat2

rep2 = repair pnat2 nat2

plotrep m = plotList [Title "Re-pairing"] (map f xs) where 
  xs=[0..2^m-1]
  f =(as nat fun) . reverse . (as fun nat)
   
main = print (take 16 (hyper_primes mset_unpair))

pchain unpairF pairG = pairG . unpairF

plotHill t n = plotList [] (hill t n)

plotHills t m = plotss (map (hill t) [0..2^m-1])

hfsHills m = plotHills hfs_pars m

data BinT  = Vr Int | Nd BinT BinT deriving (Show, Eq)

-- binary tree generator
bintrees n = bt n 0 
        
bt 1 k = [Vr k]
bt n k = [Nd l r | i<-[1..n-1], l <- bt i k, r <- bt (n-i) (k+i)]

lsum x y = a+b where (a,b)=bitunpair ((bitpair (0,x)) + (bitpair (0,y)))

-- pairings and involutions
coPair invF pF (x,y) = invF (pF (invF x, invF y))
coUnpair invF uF z = (invF x,invF y) where (x,y)=uF (invF z) 


-- multiplication and pairing/tupling

guntriple  z=(pred g,pred x,pred y) where 
  (a,b)=mset_unpair z
  a'=succ a
  b'=succ b
  g=gcd a' b'
  x=a' `div` g
  y=b' `div` g

gtriple (g,x,y) = z where
  g'=succ g
  x'=succ x
  y'=succ y
  a=x'*g'
  b=y'*g'
  z=mset_pair (pred a,pred b)  
  
rprod x y = (m,z) where
 p=mset_pair (x,y)
 m=x*y
 (q,r)=quotRem (1+p) (1+m)
 z=bitpair (q,r)

qprod x y = (1+p)%(1+x*y) where
  p=mset_pair (x,y)

qfig m = plotop qprod m  

-- todo: rebase b in p*q-1
prunpair 1 = (1,1)
prunpair z = (a,b) where
  (pq,rs)=splitAt 2 (reverse (1:(to_primes z)))
  a=product pq
  b=product rs

--invF :: [I]->[[I]]
invF xs = map (map snd) zss where
  l=genericLength xs
  ys=sort (zip xs [0..l-1])
  zss=groupBy (\x y->fst x== fst y)  ys
  
subsets [] = [[]]
subsets (x:xs) = [zs|ys<-subsets xs,zs<-[ys,(x:ys)]]
 
sset t n = map (as nat t) (subsets (as t nat n)) 

tpair x y = z where -- ((x,to_base 2 x),(y',to_base 2 y')) where
   n=max (ilog22 x) (ilog22 y)
   y'=shiftL y (fromIntegral (exp2 n))
   z=x .&. y' 

ilog22 x = head [i |i<-[0..], exp22 i > x]

ilog2 x = head [i |i<-[0..], exp2 i > x]

exp22 = exp2 . exp2

exp2 :: N->N
exp2 n = bit (fromIntegral n)

ttpair x y = z where
  xs=as bits1 nat x
  ys=as bits1 nat y
  l=genericLength xs
  r=genericLength ys
  m=max l r
  m'=exp2 (ilog2 m)
  xs'=genericTake m' (xs ++ repeat 0)
  ys'=genericTake m' (ys ++ repeat 0)
  xs''=dropLast xs' 
  ys''=dropLast ys' 
  zs=xs'++ys''
  z=as nat bits1 zs

--dropLast = reverse . tail . reverse
  
txpair a b = z where
   x=a
   y=b
   n=max (ilog22 x) (ilog22 y)
   y'=(exp22 n)*y
   x'=x .&. ((exp22 n)-1)
   z=x' .|. y' 

{-
data PL a = 
  Atom a | Tie (PL a) (PL a) | Zip (PL a) (PL a) 
  deriving (Eq,Read,Show)

pl2l (Atom a) = (0,[a])
pl2l (Tie x y) = (pl2l x) ++ (pl2l y)


data Op a b= Tie a b| Zip a b deriving (Eq,Read,Show)
data PF a = At a | PF (Op (PF a) (PF a)) deriving (Eq,Read,Show)

data PListF f a = Zero a | Succ (f (a , a )) deriving (Eq,Read,Show)
-}

fbpair x y = z where
  xs=as bits nat x
  ys=as bits nat y
  lx=genericLength xs
  bs=to_base1 lx
  zs=bs++xs++ys
  z=as nat bits zs
 
to_base1 x = (replicate (x-1) 0) ++ [1]

orderTag x y | x<y = (0,x,y-x-1)
orderTag x y = (1,y,x-y)  

dropLast = reverse . tail . reverse
  
pair_mn v m n l r =
  ite_ (var_mn m n v) l r

pair_n v n (l,r) = pair_mn v (bigone n) n l r
unpair_n v n tt | tt <= m= unpair_mn v m n tt where m=bigone n

pairn n (l,r) = pair_n (n-1) n (l,r)
unpairn n tt = unpair_n (n-1) n tt

pair0 n (l,r) = pair_n 0 n (l,r)
unpair0 n tt = unpair_n 0 n tt

xPX x = x+2^x

mprint f m = ((mapM_ print) . (map f)) [0..2^m-1]  


fix2 unpairop op x= uncurry op (unpairop x)

plotfix n = plotf (fix2 bitunpair (*)) n

plotnfix n = plotList [] (nfix2 bitunpair lcm n)

nfix2 unpairop op x = 
  f [x] where
    f xs = ys   where
     x=head xs
     y=fix2  unpairop op x
     ys=if y `elem` xs then xs else f (y:xs)
     
hUnp z = (x,y) where
  (q,r)=quotRem z 2
  x=q
  y'=z `xor` q
  y=2*y'+r

  
-- split z in a sum
  
unsum z = (x',y') where
  (x,y)=bitunpair z
  x'=bitpair (x,0)
  y'=bitpair (0,y)
      
-- recursive product emulation 

unsum1 z | z<2=(0,z)
unsum1 z = (succ x,succ y) where
  (x,y)=unsum (pred (pred z))
  
pprod 0 _ = 0
pprod _ 0 = 0
pprod 1 x = x
pprod x 1 = x
pprod a b = p where
 (x,y)=unsum1 a
 (u,v)=unsum1 b
 l=(pprod x u) + (pprod y v)
 r=(pprod x v) + (pprod y u)
 p=l + r

hf x = x `div` 2
db x = 2*x

lunpair z=(bitclip z,hf (bitclip (db z)) )

xorf x = x `xor` (db x) :: Integer

xorftest=map (bitclip . xorf . bitlift) [0..15]

-- product in terms of hd,tl

hdtest x y = (hd (x*y), (hd x)+(hd y))

tltest x y = (tl (x*y), tx*(ty+1) + ty*(tx+1)) where 
  tx=tl x
  ty=tl y
   
tprod 0 _ = 0
tprod _ 0 = 0   
tprod x y = p where
  hx=hd x
  tx=tl x
  hy=hd y
  ty=tl y
  h=hx+hy
  t1= tprod tx (ty+1)
  t2= tprod ty (tx+1)
  -- 2*tx*ty+(tx+ty)
  t=t1+t2
  p=cons h t
   
  -- (2*(tl (x*y))+1,(2*(tl x)+1)*(2*(tl y)+1))
  -- (tl (x*y), (tl x),(tl y), (2*(tl x)+1)*(2*(tl y)+1)) 
  -- (2a+1)*(2b+1) ==
  -- 4ab+2a+2b+1 
  -- 2*(tl (x*y)+1)=(2*(tl x)+1)*(2*(tl y)+1))
  
  -- 2 txy +1 =(2 tx+1)*(2 ty+1)
  -- 2 txy+1=4 tx ty + 2(tx+ty) + 1
  -- 2 txy = 4 tx ty + 2tx + 2ty
  --  txy= 2 tx ty + tx+ty
  -- txy = tx ty + tx + tx ty + ty
  -- txy = tx (ty+1) + ty (tx+1)
  
j' x y = pepis_pair (x,y)
  
{-  
syrp x = (a+1,b) where 
  (a,b)=pprod 3 x
-}

-- from J.Robinson 1967: we write j' x y = j y x
--j'(0,x)=2x
--j'(s(y),x)=2j'(y,x) +1 = s j'

-- jS x y = P(x)   

-- (a+b)^2 = a^2+2*a*b+b^2
{-
(a+1)*(b+1)=ab+a+b+1

a+b=(a+1)*(b+1)-(ab+1)

2^x*(2y+1)+
2^u*(2v+1)
----------
2^m[*(2^x')(2y+1)+
     (2^u')(2x+1)
   ]

-}

--2^(x+1)z=2^xz+2^xz

a 0 x = x
a x 0 = x
a x y = a1 h t y where
  h=hd x
  t=tl x
  
a1 0 t y = succ (a t (a t y))  
a1 h t y = z where
  halfx = cons (pred h) t
  r=a halfx y
  z=a halfx r

-- 2a+b=a+a+b  
 
 {-
 s:: n->n
   
   s x | e_ x = c e e
   s x | e_ (h x) = c (s k) (t y) where
      y=s (t x)
      k=h y
   s x = c e (c (p k) y) where 
      k=h x
      y=t x

   p :: n->n   
   p x | e_ (h x) && e_ (t x) = e
   p x | e_ x'= c (s k) (t x) where
      x'=h x
      y=t x
      k=h y
   p kxs = c e (p (c (p k) xs)) where
      k=h kxs
      xs=t kxs
-}        

var' 1 0 = 1
var' n k | 0<=k && k < n' = bitpair (k',k') where 
  n'=pred n
  k'=var' n' k
var' n k | k==n' = bitpair (m,0) where 
  n'=pred n
  m=bigone n'

lastvar 1 = 1
lastvar n = bitpair ((var' n 0),0)

vars' n = map (var' n) [0..n-1]

vtest n = mapM_ print (map (as bits1 nat) (vars' n))


bl 0 = 0
--bl 1 = 1
bl n = db (db (bl (hf n)))+(n `mod` 2)

infixr 1 >:

a >: b = b . a

infixr 1 <:

a <: b = b  a

--  seq encoding that counts 0s then 1s

-- BUG: bfun2nat [2,0]
bfun2nat []=0
bfun2nat [0]=1
bfun2nat [1]=2
bfun2nat (n:ns) = succ (succ (as nat bits bs)) where
  bs=f n ns
  f _ []=[]
  f b (x:xs) = (genericTake (succ x) (repeat b)) ++ (f (g b) xs)
  g 0=1
  g 1=0
 
nat2bfun 0 =[]
nat2bfun 1 =[0]
nat2bfun 2= [1]  
nat2bfun n = (head bs):ns where
  bs=as bits nat (pred (pred n))
  ns=bs2ns bs
  bs2ns xs = ks where
    ks=map (pred.genericLength) (group xs)

-- prime related N->N automorphisms  
p2m n = as nat mset (as pmset nat n)
m2p n = as nat pmset (as mset nat n)

p_m n = (fromIntegral (p2m n)) / (fromIntegral (m2p n))  
m_p n = (fromIntegral (m2p n)) / (fromIntegral (p2m n)) 

n_g n =  (fromIntegral (nat2gray n)) / (fromIntegral (gray2nat n)) 

-- modifiers


--zest :: Iso a b -> Iso b b -> Iso a b
--zest mm fg = compose fg mm

--- distr mprimes vs. primes

mdist n = (fromIntegral (n)) / (fromIntegral (2^n))

pdist x = (x) / (log x)

{- done: mprod'
mprod_ 0 _ = 0
mprod_ _ 0 = 0
mprod_ x y | x>0 && y>0 = succ (mprod (pred x) (pred y))
-}

corprods n |n>1= [(x,y)|x<-ns,y<-ns, mprod' x y == x*y] where ns=[2..2^n-1]

--------


pfactors n =  nub (to_primes n)

-- rad(n) : A007947
rad n = product (pfactors n)
ppfactors n = nub (as pmset nat n)
pmfactors n = nub (as mset nat n)

pprad n =  as nat set (ppfactors n)
pmrad n =  as nat set (pmfactors n)

pprad' n =  product (ppfactors n)
pmrad' n =  product (pmfactors n)

{-
map set of sq free primes to sq free primes

compare: rad(n) with pprad
    
-}  

auto_p2m 0 = 0
auto_p2m n = as nat mset (as pmset nat n)

auto_m2p 0 = 0   
auto_m2p n = as nat pmset (as mset nat n)   

xorLeft :: N->N
xorLeft n = n `xor` (shiftL n 1)

xorRight :: N->N
xorRight n = n `xor` (shiftR n 1)

-- xorRight == xorLeft . (2*)

-- pairing - similar to Pepis but using 0's on the left in base 1 as x

logcons x y = 2^(x+e)+y where e=ilog2 y
logdecons z = (x,y) where 
  xe=ilog2 z-1
  y=z-2^xe
  e=ilog2 y
  x=xe-e

logpair (x,y)=pred (logcons x y)
logunpair z = logdecons (succ z)
   
-- fix-free parenthesis code as number   
parnum n = as nat bits (as hff_pars nat n)

-- dual of fix-free parenthesis code as number
dparnum n = as nat bits ds where
  ps=as hff_pars nat n
  rs=reverse ps
  ds=map (\x->1-x) rs

-- same in par/dual par
autopars n = [x|x<-[0..n-1],parnum x==dparnum x]

{- 
-- tagged with () - to say they represent, for instance, atoms 
rtag n = as nat pars ("(()"++(as pars nat n)++")")  

runtag = (as nat pars) . runtagpars . (as pars nat) where
  runtagpars ('(':'(':')':xs) = '(':xs 
  runtagpars xs = xs
-}

-- based on counting 0s and 1s in the bijective base 2 representation
nat2gfun n = map pred ls where
  ns=nat2bits (db n)
  gs=group ns
  ls=map genericLength gs
  
gfun2nat ns = hf (bits2nat bs) where 
  ks=map succ ns
  repeatK k n = genericTake k (repeat n)
  bss=zipWith repeatK ks (map parity [1..])
  bs=concat bss

nat2gfun' n = map pred ls where
  ns=nat2bits (succ (db n))
  gs=group ns
  ls=map genericLength gs
  
gfun2nat' ns = hf (bits2nat bs) where 
  ks=map succ ns
  repeatK k n = genericTake k (repeat n)
  bss=zipWith repeatK ks (map parity [0..])
  bs=concat bss
    

