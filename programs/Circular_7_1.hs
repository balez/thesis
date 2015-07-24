-- * CHAPTER 7. Circular Traversals using Attribute Grammars
-- ** GHC Options
{-# LANGUAGE
     ExistentialQuantification
    , TypeOperators
    , NoMonomorphismRestriction
    , Arrows
    , MultiParamTypeClasses -- class Fix
    , FunctionalDependencies
    , FlexibleInstances
    , DeriveFunctor
    , FlexibleContexts
    , RankNTypes
    , UndecidableInstances -- for instance ArrowCata TEnv
    , PolyKinds
    , LambdaCase
    , GADTs
    , BangPatterns
 #-}

-- ** Module and Imports
module Circular_7_1 where
import Circular_6_1and2
import Circular_6_3

import Prelude hiding (id, (.), reverse)
import Control.Category
import Control.Arrow

-- * 7.1 Palindrome
-- **  The Problem
-- page 91
palindrome :: (Eq a) => [a] -> Bool
palindrome x = x == reverse x
-- page 91
eqlist [] [] = True
eqlist (x:xs) (y:ys) = x == y && eqlist xs ys
eqlist _ _ = False
-- page 92
reverse xs = revcat xs []
revcat [] ys = ys
revcat (x:xs) ys = revcat xs (x:ys)
-- **  Bird's Solution
-- page 92
eqrev x y z = (eqlist x y, revcat x z)
-- page 92
palindrome1 x = eq where (eq, rev) = eqrev x rev []
-- page 92
eqrev1 []     []     zs = (True, zs)
eqrev1 (x:xs) (y:ys) zs = (x == y && t, r)
  where (t,r) = eqrev1 xs ys (x:zs)
-- page 92
eqrev2 []       ys zs  =  (True, zs)
eqrev2 (x : xs) ys zs  =  (x == head ys && t, r)
  where (t,r) = eqrev2 xs (tail ys) (x : zs)
-- page 93
palindrome2 x = eq  where (eq,rev) = eqrev2 x rev []
-- page 93
{-
eqrev1 []     (y:ys) zs = (False, zs)
eqrev1 (x:xs) []     zs = (False, r)
  where (t,r) = eqrev1 xs [] (x:zs)
-}
-- **  Fixing Bird's Solution
-- page 93
eqrev3 [] ys zs = (null ys, zs)
eqrev3 (x:xs) ys zs = (eq_xxs, rev)
  where (eq_xs, rev) = eqrev3 xs (safe_tail ys) (x:zs)
        eq_xxs = case ys of
          [] -> False
          (y : ys') -> x == y && eq_xs
-- page 93
safe_tail [] = []
safe_tail (h:t) = t
-- page 93
eqrev4 [] ys zs = (null ys, zs)
eqrev4 (x:xs) ys zs = (eq_xxs, rev)
  where (eq_xs, rev) = eqrev4 xs tail_ys (x:zs)
        (eq_xxs, tail_ys) = case ys of
          [] -> (False, [])
          (y : ys') -> (x == y && eq_xs, ys')
-- page 94
palindrome4 x = eq where (eq,rev) = eqrev4 x rev []
-- page 94
palindrome4' [a,b,c] = q1
 where
   (q1, r1) = case r of                     -- "eqrev4 [a,b,c] r []"
                [] -> (False, [])
                (y : ys') -> (a == y && q2, ys')
   (q2, r2) = case r1 of                    -- "eqrev4 [b,c] r1 [a]"
                [] -> (False, [])    
                (y : ys') -> (b == y && q3, ys')
   (q3, r3) = case r2 of                    -- "eqrev4 [c] r2 [b,a]"
                [] -> (False, [])
                (y : ys') -> (c == y && q4, ys')
   (q4, r) = (null r3, [c,b,a])             -- "eqrev4 [] r3 [c,b,a]"
-- page 94
palindrome4'' [a,b,c] = q1
 where
   (q1, r1) = (a == c && q2, [b,a])
   (q2, r2) = (b == b && q3, [a])
   (q3, r3) = (c == a && q4, [])
   (q4, r)  = (True, [c,b,a])
-- page 94
palindrome4''' [a,b,c] = a == c  &&  b == b  &&  c == a  &&  True
-- **  Palindrome with ArrowCata
-- page 95
revcatAlg :: Alg (ListF a) ([a] -> [a])
revcatAlg Nil zs  =  zs
revcatAlg (Cons x revcat_xs) zs  =  revcat_xs (x:zs)
-- page 95
eqlistAlg :: Eq a => Alg (ListF a) ([a] -> Bool)
eqlistAlg Nil [] = True
eqlistAlg (Cons x eqlist_xs) (y:ys) = x == y && eqlist_xs ys
eqlistAlg _ _ = False
-- page 95
palindromeA = proc () -> do
  rev <- cataA -< revcatAlg
  eq <- cataA -< eqlistAlg
  returnA -< eq (rev [])
-- page 95
{-
runEnv  palindromeA [1,2,3] () :==> False
runCirc palindromeA [1,2,1] () :==> True
-}
-- page 95
palindrome3 x =
  let (eq,rev) = cata (pairAlg eqlistAlg revcatAlg) x
  in eq (rev [])
-- **  Pairing Higher-Order Algebras
-- page 96
hpair :: Functor f =>
  Alg f (a -> b) -> Alg f (c -> d) -> Alg f ((a, c) -> (b,d))
-- page 96
{-
(1) cata (hpair g h) x (a,c) == (cata g x a, cata h x c)
-}
-- page 96
hpair u v x (a,c) = (u (fmap (pr1 c) x) a, v (fmap (pr2 a) x) c)
-- page 96
pr1 :: c -> ((a, c) -> (b,d)) -> a -> b
pr2 :: a -> ((a, c) -> (b,d)) -> c -> d
pr1 c f a = fst $ f (a,c)
pr2 a f c = snd $ f (a,c)
-- page 96
{-
eqrev5 Nil (y, z)  :==> (null y, z)
eqrev5 (Cons h t) (y, z)
  :==> case y of
       [] -> (False, snd (eqrev5 t ([], h : z)))
       (h':t') -> ( h == h' && fst (eqrev5 t (t', z)) -- one recursive call
                 , snd (eqrev5 t (y, h : z))) -- another recursive call
-}
-- **  A New Traversal Primitive
-- page 97
data HOListAlg a i s = HOListAlg (i -> s) (a -> (i -> s) -> (i -> s))
-- page 97
{-
algCons :: a -> (i -> s) -> (i -> s)
algCons a f i = ...
-}
-- page 97
{-
algConsSpec :: a -> i -> (i, s -> s)
-}
-- page 97
{-
algCons a f i = result (f x)
  where (x, result) = algConsSpec a f i
-}
-- page 97
{-
algConsSpec2 :: a -> s -> i -> (s,i)
-}
-- page 97
{-
algCons x f i = s
  where (s,i') = algConsSpec2 x (f i') i
-}
-- page 97
data ListAG a i s = ListAG (i -> s) (a -> s -> i -> (s, i))
-- page 97
algListAG :: ListAG a i s -> Alg (ListF a) (i -> s)
algListAG (ListAG nil cons) Nil = nil
algListAG (ListAG nil cons) (Cons h t) = \ i ->
  let (s, ti) = cons h (t ti) i in s
-- page 97
eqlistLAG :: Eq a => ListAG a [a] Bool
eqlistLAG = ListAG null eqlistConsAG
-- page 98
eqlistConsAG x eq_xs [] = (False, [])
eqlistConsAG x eq_xs (y:ys) = (x == y && eq_xs, ys)
-- page 98
{-
algListAG eqlistLAG Nil ys == null ys
algListAG eqlistLAG (Cons x eq_xs) [] ==
  let (s, ti) = eqlistConsAG x (eq_xs ti) [] in s
==
  let (s, ti) = (False, []) in s
==
  False
-}
-- page 98
{-
algListAG eqlistLAG (Cons x eq_xs) (y:ys) ==
  let (s, ti) = eqlistConsAG x (eq_xs ti) (y:ys) in s
==
  let (s, ti) = (x == y && eq_xs ti, ys) in s
==
  let (s, ti) = (x == y && eq_xs ys, ys) in s
==
  x == y && eq_xs ys
-}
-- page 98
revcatLAG :: ListAG a [a] [a]
revcatLAG = ListAG id (\x rev_xs zs -> (rev_xs, x:zs))
-- page 98
pairListAG :: ListAG a i s -> ListAG a i' s' -> ListAG a (i,i') (s,s')
pairListAG (ListAG n1 c1) (ListAG n2 c2) = ListAG n c
 where
   n ~(i1,i2) = (n1 i1, n2 i2)
   c x (s1,s2) ~(i1,i2) = transpose (c1 x s1 i1, c2 x s2 i2)
-- page 98
transpose (~(a,b),~(c,d)) = ((a,c),(b,d))
-- page 98
eqrev5 = cata $ algListAG $ pairListAG eqlistLAG revcatLAG
