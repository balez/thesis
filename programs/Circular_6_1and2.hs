-- * CHAPTER 6. Circular Traversals Compositionally
-- ** GHC Options
{-# LANGUAGE
     ExistentialQuantification
    , TypeOperators          -- arrow operators
    , Arrows
    , MultiParamTypeClasses  -- class Fix
    , FunctionalDependencies -- class Fix
    , FlexibleInstances      -- class ArrowCata
    , DeriveFunctor          -- TreeF
    , FlexibleContexts       -- ArrowCata TreeF
    , UndecidableInstances   -- for instance ArrowCata TEnv
    , PolyKinds
 #-}

-- ** Module and Imports
module Circular_6_1and2 where
import Prelude hiding (id, (.), reverse)
import Control.Category
import Control.Arrow

-- ** Arrow operator
infixr 1 -
infixr 0 ~>
type (-) x (c :: * -> * -> *) = c x
type (~>) cx y = cx y

{-
x  -c~>  y  -d~>  z
is parsed as
c x (d y z)
x `c` (y `d` z)
-}
-- * 6.1 Introduction
-- page 73
{-
let x₁ = A₁
    x₂ = A₂
    ⋯
    xₙ = Aₙ
 in E
-}
-- page 73
{-
let (x₁,⋯,xₙ) = (A₁,⋯,Aₙ)
 in E



-}
-- **  Example, Repmin
-- page 74
data Tree = Leaf Int | Fork Tree Tree
-- page 74
minTree (Leaf x) = x
minTree (Fork l r) = min (minTree l) (minTree r)
-- page 74
replace y (Leaf x) = Leaf y
replace y (Fork l r) = Fork (replace y l) (replace y r)
-- page 74
repMin tree = replace (minTree tree) tree
-- page 74
repMin' tree =
  let min = minTree tree
      rep = replace min tree
  in rep
-- page 74
repMin'' tree =
  let (min, rep) = (minTree tree, replace min tree)
  in rep
-- page 74
repMinCirc tree =
  let (min, rep) = min_and_replace min tree
  in rep
-- page 74
min_and_replace y (Leaf x) = (x, Leaf y)
min_and_replace y (Fork l r) = (min ml mr, Fork tl tr)
  where (ml, tl) = min_and_replace y l
        (mr, tr) = min_and_replace y r
-- **  Issues With the Transformation
-- ****    Diverging programs
-- ****    Complex and non-modular programs
-- ****    Attribute Grammars
-- ****    Our Solution for Compositionality
-- page 76
{-
repMinA = proc () -> do
  m <- minA -< ()
  replaceA -< m
-}
-- page 76
{-
repMin tree =
  let m = minTree tree
   in replace m tree
-}
-- ****    Overview
-- * 6.2 Abstract Programming Interface for Computations over a Data Structure
-- page 77
{-
class Category h where
  id  :: a -h~> a
  (.) :: b -h~> c  ->  a -h~> b  ->  a -h~> c
-}
-- page 77
{-
import Prelude hiding (id, (.))
import qualified Prelude
instance Category (->) where
 id = Prelude.id
 (.) = (Prelude..)
-}
-- page 78
{-
class Category h => Arrow h where
  arr   :: (a -> b)  ->   a    -h~>  b
  first ::  a -h~> b   ->  (a,c) -h~> (b,c)
-}
-- page 78
{-
&&& :: c -h~> a   ->  c -h~> b  ->  c -h~> (a,b)
f &&& g = arr swap . first g . arr swap . first f . arr dup
  where dup x = (x,x)
        swap (x,y) = (y,x)
arr fst :: (a,b) -h~> a
arr snd :: (a,b) -h~> b
-}
-- page 78
{-
example' f g h j =
  proc (x,y) -> do
    a <- f -< x
    b <- g -< h a y
    returnA -< j b
-}
-- page 78
{-
example'' f g h j =
 \(x,y) ->
    let a = f x
        b = g (h a y)
     in j b
-}
-- page 78
{-
example :: (Arrow h) =>
  (a -h~> b) -> (c -h~> d) -> (b -> p -> c) -> (d -> q) -> (a,p) -h~> q
example f g h j  =  arr j . g . arr (uncurry h) . first f
-}
-- **  The Environment Arrow
-- page 79
newtype Env e a b = Env {runEnv :: e -> a -> b}
-- page 79
instance Category (Env e) where
  id = arr id
  Env g . Env f = Env (\e -> g e . f e)
-- page 79
instance Arrow (Env e) where
  arr f = Env $ const f
  first (Env f) = Env $ \ e (x,y) -> (f e x, y)
-- page 79
minEnv :: Env Tree () Int
minEnv = Env $ \t () -> minTree t
-- page 79
replaceEnv :: Env Tree Int Tree
replaceEnv = Env $ \t y -> replace y t
-- page 79
repMinEnv = proc () -> do
  m <- minEnv -< ()
  replaceEnv -< m
-- **  A primitive to define traversals
-- ***   Algebras and Catamorphisms
-- page 80
class Functor f => Fix f t | t -> f where
  out :: t -> f t
  inn :: f t -> t
-- page 80
data TreeF r = LeafF Int | ForkF r r deriving Functor
instance Fix TreeF Tree where
  out (Leaf x)    = LeafF x
  out (Fork l r)  = ForkF l r
  inn (LeafF x)   = Leaf x
  inn (ForkF l r) = Fork l r
-- page 80
type Alg f t = f t -> t
-- page 80
cata :: (Fix f t) => Alg f r -> t -> r
cata alg = phi
  where  phi = alg . fmap phi . out
-- page 80
minAlg (LeafF x)   = x
minAlg (ForkF l r) = min l r
-- page 80
mapTreeAlg f (LeafF x)   = Leaf (f x)
mapTreeAlg f (ForkF l r) = Fork l r
-- page 80
replaceAlg y = mapTreeAlg (const y)
-- ***   Extending the Abstract Interface
-- page 81
class (Arrow h, Functor f) => ArrowCata f h | h -> f where
  cataA :: Alg f x -h~> x
-- page 81
instance (Fix f t) => ArrowCata f (Env t) where
  cataA = Env $ flip cata
-- page 81
minA :: ArrowCata TreeF h => () -h~> Int
minA = proc () -> cataA -< minAlg
-- page 81
replaceA :: ArrowCata TreeF h => Int -h~> Tree
replaceA = proc y -> cataA -< replaceAlg y
-- page 81
repMinA :: ArrowCata TreeF h => () -h~> Tree
repMinA = proc () -> do
  m <- minA -< ()
  replaceA -< m
-- ****    Polymorphic encoding of inductive datatypes
