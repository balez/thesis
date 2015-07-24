-- * CHAPTER 6. Circular Traversals Compositionally
-- ** GHC Options
{-# LANGUAGE
     ExistentialQuantification
    , TypeOperators
    , NoMonomorphismRestriction
    , Arrows
    , FunctionalDependencies
    , FlexibleInstances
    , DeriveFunctor
    , FlexibleContexts
    , BangPatterns
 #-}

-- ** Module and Imports
module Circular_6_3 where
import Circular_6_1and2

import Prelude hiding (id, (.), reverse)
import Control.Category
import Control.Arrow

-- * 6.3 Circular Implementation
-- **  Recursive Pattern for Circular Traversals
-- page 82
pairAlg :: Functor f => Alg f i -> Alg f j -> Alg f (i,j)
pairAlg alpha beta = \y -> (alpha (fmap fst y) , beta (fmap snd y))
-- page 82
min_and_replace' :: Int -> Tree -> (Int, Tree)
minReplaceAlg :: Int -> Alg TreeF (Int, Tree)
-- page 82
min_and_replace' y t = cata (minReplaceAlg y) t
minReplaceAlg y = minAlg `pairAlg` replaceAlg y
-- page 82
{-
repMinCirc tree = newtree
  where (minimum, newTree) = min_and_replace minimum tree
-}
-- page 82
type CircBody f s r = s -> (Alg f s , r)
-- page 82
repMinBody :: CircBody TreeF (Int,Tree) Tree
repMinBody (minimum, newTree) = (minReplaceAlg minimum, newTree)
-- page 83
circFix :: Fix f t => CircBody f s r -> t -> r
circFix body structure = result
  where (alg, result) = body (cata alg structure)
-- page 83
repMinCirc1 = circFix repMinBody
-- page 83
repMinCirc2 inputTree = resultTree
  where (alg, resultTree) = repMinBody (minimum, newTree)
        (minimum, newTree) = cata alg inputTree
-- page 83
repMinCirc3 inputTree = resultTree
  where (alg, resultTree) = (minAlg `pairAlg` replaceAlg minimum, newTree)
        (minimum, newTree) = cata alg inputTree
-- page 83
repMinCirc4 inputTree = newTree
  where (minimum, newTree) = min_and_replace minimum inputTree
-- **  ArrowCata Instance
-- page 84
data Circ f a b = forall s . C {runC :: a -> CircBody f s b}
runCirc :: Fix f t => Circ f a b -> t -> a -> b
runCirc (C circ) t x = circFix (circ x) t
-- page 84
{-
C :: (∃ s . a -> CircBody f s b) -> Circ f a b
-}
-- ***   Type Class Homomorphisms
-- page 84
circEnv :: Fix f t => Circ f a b -> Env t a b
circEnv = Env . runCirc
-- page 84
{-
circEnv id == id
circEnv (g . f) == circEnv g . circEnv f
circEnv (arr f) == arr f
circEnv (first f) == first (circEnv f)
circEnv cataA == cataA
-}
-- ***   Composition
-- page 85
{-
f :: a -> s -> (alg fun s, b)
g :: b -> t -> (alg fun t, c)
-}
-- page 85
compCirc g f = \x ~(s,t) ->
  let (f_alg, b) = f x s
      (g_alg, c) = g b t
   in (pairAlg f_alg g_alg, c)
-- ***   Lifting non-traversals
-- page 85
arrCirc f = \x _ -> (const (), f x)
-- ***   Pairing
-- page 85
firstCirc f = \ (a, c) s ->
  let (alg, b) = f a s
   in (alg, (b, c))
-- ***   Catamorphisms
-- page 85
{-
(,) :: Alg fun s -> s -> (Alg fun s, s)
-}
-- ***   Class Instances
-- page 86
instance Functor f => Category (Circ f) where
  id = arr id
  C g . C f  = C $ compCirc g f
-- page 86
instance Functor f => Arrow (Circ f) where
  arr f = C $ arrCirc f
  first (C f) = C $ firstCirc f
-- page 86
instance Functor f => ArrowCata f (Circ f) where
  cataA = C (,)
-- ***   Example
-- page 86
{-
repMinCirc t == runCirc repMinA t ()
-}
-- ***   Proving the Homomorphism Properties
-- page 86
{-
circEnv $ C f
  == Env $ runCirc $ C f
  == Env $ \t x -> circFix (f x) t
  == Env $ \t x -> let (a,r) = f x (cata a t) in r
-}
-- **** circEnv (arr f) == arr f
-- page 86
{-
circEnv (arr f)
  == circEnv (C (arrCirc f))
  == Env $ \t x -> let (a,r) = arrCirc f x (cata a t) in r
  == Env $ \t x -> let (a,r) = (const (const (), f x)) (cata a t) in r
  == Env $ \t x -> let (a,r) = (const (), f x) in r
  == Env $ \t x -> f x
  == Env $ const f
  == arr f
-}
-- **** circEnv id == id
-- page 86
{-
circEnv id
  == circEnv (arr id)
  == arr id
  == id
-}
-- **** circEnv (C g . C f) == circEnv g . circEnv f
-- page 87
{-
circEnv (C g . C f)
  == circEnv $ C $ compCirc g f
  == Env $ \t x -> let (a,r) = compCirc g f x (cata a t) in r
  == Env $ \t x -> let (f_a, y) = f x (fst p)
                       (g_a, z) = g y (snd p)
                       p        = cata (pairAlg f_a g_a) t
                    in z

  -- cata (pairAlg f_a g_a) t == (cata f_a t, cata g_a t)

  == Env $ \t x -> let (f_a, y) = f x (cata f_a t)
                       (g_a, z) = g y (cata g_a t)
                    in z
  == Env $ \t x -> circFix (g (circFix (f x) t)) t
  == Env $ \t -> runCirc (C g) t . runCirc (C f) t
  == Env (runCirc (C g)) . Env (runCirc (C f))
  == circEnv g . circEnv f
-}
-- **** circEnv (first f) == first (circEnv f)
-- page 87
{-
circEnv $ first $ C f
  == circEnv $ C $ firstCirc f
  == Env $ \t x -> let (a,r) = firstCirc f x (cata a t) in r
  == Env $ \t (y,z) -> let (a,r) = let (a',b) = f y (cata a t)
                                    in (a', (b,z))
                        in r
  == Env $ \t (y,z) -> let (a, b) = f y (cata a t) in (b,z)
  == Env $ \t (y,z) -> (let (a, b) = f y (cata a t) in b, z)
  == Env $ \t (y,z) -> (circFix (f y) t, z)
  == Env $ \t (y,z) -> (runCirc (C f) t y, z)
  == first $ Env $ runCirc $ C f
  == first $ circEnv $ C f
-}
-- **** circEnv cataA == cataA
-- page 87
{-
circEnv cataA
  == circEnv (C (,))
  == Env $ \t x -> let (a,r) = (,) x (cata a t) in r
  == Env $ \t x -> cata x t
  == cataA
-}
-- ***   Kleisli Arrow for an Indexed Monad
-- ****    Arrows are Preferable over Indexed Monads for Circular Programs
-- **  List of Deviations
-- page 88
deviations xs =
 let mean = sum xs / fromIntegral (length xs)
  in map (\x -> x - mean) xs
-- page ??
deviations2 xs = m
  where (l,s,m) = lsm (\x -> x - (s / fromIntegral l)) xs
-- page ??
lsm f = go
  where go [] = (0,0,[])
        go (h:t) = let (l,s,m) = lsm f t
                     in (l+1, s+h, f h : t)
-- page ??
deviations3 xs = m
  where (!l,!s,!m) = lsm3 (\x -> x - (s / fromIntegral l)) xs
-- page ??
lsm3 f = go
  where go [] = (0,0,[])
        go (h:t) = let !(!l,!s,!m) = lsm3 f t
                     in (l+1, s+h, f h : m)
-- page 88
data ListF a x = Nil | Cons a x deriving Functor
instance Fix (ListF a) [a] where
  out []         = Nil
  out (h : t)    = Cons h t
  inn Nil        = []
  inn (Cons h t) = h : t
-- page 89
listAlg :: b -> (a -> b -> b) -> Alg (ListF a) b
listAlg n c Nil = n
listAlg n c (Cons h t) = c h t
-- page 89
sumAlg    :: Num a => Alg (ListF a) a
lengthAlg :: Num b => Alg (ListF a) b
mapAlg    :: (a -> b) -> Alg (ListF a) [b]
-- page 89
sumAlg    = listAlg 0 (+)
lengthAlg = listAlg 0 ((+) . const 1)
mapAlg f  = listAlg [] ((:) . f)
-- page 89
sumA    :: (ArrowCata (ListF a) t, Num a) => t () a
lengthA :: (ArrowCata (ListF a) t, Num a) => t () a
mapA    :: ArrowCata (ListF a) t          => t (a -> b) [b]
-- page 89
sumA    = proc () -> cataA -< sumAlg
lengthA = proc () -> cataA -< lengthAlg
mapA    = proc f  -> cataA -< mapAlg f
-- page 89
deviationsA :: (ArrowCata (ListF b) t, Fractional b) => t () [b]
deviationsA = proc () -> do
  sum <- sumA -< ()
  len <- lengthA -< ()
  let mean = sum / len
  mapA -< (\x -> x - mean)
-- ****    Avoiding Intermediate Bindings
-- page 90
constArr :: Arrow t => b -> t x b
appArr :: Arrow t => t x (a -> b) -> t x a -> t x b
-- page 90
constArr = arr . const
appArr f g = proc x -> do
  y <- f -< x
  z <- g -< x
  returnA -< y z
-- page 90
liftArr :: Arrow t => (a -> b) -> t x a -> t x b
liftArr2 :: Arrow t => (a -> b -> c) -> t x a -> t x b -> t x c
liftArr3 :: Arrow t =>
  (a -> b -> c -> d) -> t x a -> t x b -> t x c -> t x d
-- page 90
liftArr  f a     = constArr f `appArr` a
liftArr2 f a b   = liftArr f a `appArr` b
liftArr3 f a b c = liftArr2 f a b `appArr` c
-- page 90
deviationsA' = proc () -> do
  mean <- liftArr2 (/) sumA lengthA -< ()
  mapA -< (\x -> x - mean)
