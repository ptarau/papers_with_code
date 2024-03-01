module Visuals where

import Data.List
import Data.Graph.Inductive
import Graphics.Gnuplot.Simple

-- plots

-- plot 1 f
plotl xs = plotList [] xs

plotf f m = plotList [] (map f [0..2^m-1])

-- plot list of fs

plotfs fs m = plotfsx fs 0 m

plotfs1 fs m = plotfsx fs 1 m

plotfsx fs o0 m = plotLists [] (mapl fs m) where
  mapl fs m = map appl fs
  appl f =  map f [o0..2^m-1]

plotls xss =  plotLists [] xss
      
-- as spacefilling curve f:N->(N,N)
pplot = pplotx []

pplotx attrs f m = plotPath attrs (map (to_ints . f) [0..2^m-1])

plotpairs ps = plotPath [Aspect (Ratio 1)] (map to_ints ps)

plot_unpairing f m = plotpairs (map f [0..2^m-1])

to_ints :: (Integer,Integer)->(Int,Int)
to_ints (i,j)=(fromIntegral i,fromIntegral j)

-- 3d plots

plot3d f xs ys = plotFunc3d [Title ""] [] xs ys f

plotpairing f m = plot3d (curry f) ls ls where ls=[0..m-1]


-- graphviz tools

-- list of labeled edges to inductive graph

es2gr :: (Ord a) => [(a, a, t)] -> Gr a t
es2gr es = mkGraph lab_vs lab_es where 
  vs=to_vertices es
  lab_vs=zip [0..] vs
  lab_es=to_edges vs es

-- list of pairs/unlabeled edges to inductive graph
  
ps2gr :: (Ord a) => [(a, a)] -> Gr a ()
ps2gr ps = es2gr (map no_label ps) where
  no_label (a,b) = (a,b,())

ps2bgr :: (Ord a,Show a) => [(a, a)] -> Gr String ()
ps2bgr ps = es2gr (map no_label ps) where
  no_label (a,b) = ((""++show a),(show b)++"'",())
  
to_vertices es = sort $ nub $ concatMap f es where
  f (from,to,_label)=[from,to]
  
to_edges vs es = map (f vs) es where
  f vs (x,y,l) = (lookUp x vs,lookUp y vs,l)    
  lookUp n ns = i where Just i=elemIndex n ns


-- generators 
nat2es f n = nat2edges e f n where  e n m i = (n,m,i)

nat2ps f n = nat2edges e f n where e n m _ = (n,m,())

nat2hd_tl_es hd tl n = nat2es f n where f x = [hd x,tl x]
    
nat2unpair_es uf n = nat2es f n where
  f 0 = []
  f z = [x,y] where 
    (x,y)=uf (pred z) 
                                    
-- helper
nat2edges e f n = nub (nat2es0 f n) where
  nat2es0 _ 0 = []
  nat2es0 f n = (zipWith (e n) ms [0..]) ++ 
              (concatMap (nat2es0 f) ms) where 
                 ms=f n   
 
-- graphviz interface
                 
eviz es = gviz (es2gr es)
  
pviz ps = gviz (ps2gr ps)

bviz ps = gviz (ps2bgr ps)
  
gviz g = writeFile "gr.gv" 
  ((graphviz g "" (0.0,0.0) (2,2) Portrait)++"\n")

-- graphviz examples

gfig f n = eviz (nat2ps f n)
gfigx f n = eviz (nat2es f n)
gfig2 f n = eviz (nat2unpair_es f n)

cfig deconser n = eviz ps where
  ps = nat2hd_tl_es (fst.deconser) (snd.deconser) n

--  gfig1 bitunpair 42  

-- examples

-- plots
plot1 x = plotf plot1a x
plot1a x=toRational (z/log z) where z=fromIntegral x

plot2 m = plotfs [f,g] m where
  f x= toRational (x + 1)
  g x= toRational (2*x)
  
 
-- gviz graphs

gv1 = eviz [(1111111111, 222222222222222222222,"a"),(1111111111,10,"b"),(10,20,"c")]

gv2 = pviz [(10,20),(20,30),(30,10)]
            

{-
  


as_natg_nat = nat2es as_nats_nat

as_mg_nat = nat2es (as mset nat)

as_sg_nat = nat2ps (as set nat)
 
fig1=eviz . as_pairg_nat
fig2=eviz . as_natg_nat
fig3=eviz . as_mg_nat
fig4=eviz . as_sg_nat 

-}