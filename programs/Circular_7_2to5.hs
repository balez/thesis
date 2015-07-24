-- * CHAPTER 7. Circular Traversals using Attribute Grammars
-- ** GHC Options
{-# LANGUAGE
      TypeOperators
    , NoMonomorphismRestriction
    , Arrows
    , MultiParamTypeClasses -- class Fix, FixW
    , FunctionalDependencies
    , FlexibleInstances
    , FlexibleContexts
    , RankNTypes
    , UndecidableInstances -- for instance "ArrowAG f (Env t)"
    , LambdaCase
    , GADTs
    , EmptyCase
 #-}

-- ** Module and Imports
module Circular_7_2to5 where
import Circular_6_1and2

import Prelude hiding (id, (.))
import Control.Category
import Control.Arrow

-- * 7.2 Attribute Grammars
-- **  AG Implementations
-- ****    First Class AG
-- ****    Zipper Based AG
-- **  Generic AG Rules
-- ****    Weakly Typed AG Implementation
-- page 100
type SimpleAG c i s = c -> (i, [s]) -> (s, [i])
-- page 100
data TreeG c = Node c [TreeG c]
-- -- ****    Generic Tree Traversals
-- page 100
data ListC a = ConsC a | NilC     -- list constructors
listToTree :: [a] -> TreeG (ListC a)
listToTree [] = Node NilC []
listToTree (x : xs) = Node (ConsC x) [listToTree xs]
-- page 100
runSimpleAG :: SimpleAG c i s -> TreeG c -> i -> s
runSimpleAG g (Node c tt) i = s
  where (s, ii) = g c (i, ss)
        ss = zipWith (runSimpleAG g) tt ii
-- ****    Bijective Generic Tree Representation
-- page 101
data TreeW c = forall p . NodeW (c p) (p (TreeW c))
-- page 101
data V0 x = V0
data V1 x = V1 x
data ListS a p where
  ConsS :: a -> ListS a V1
  NilS  :: ListS a V0
-- page 101
listToTreeW :: [a] -> TreeW (ListS a)
listToTreeW [] = NodeW NilS V0
listToTreeW (x : xs) = NodeW (ConsS x) (V1 $ listToTreeW xs)
-- page 101
treeWToList :: TreeW (ListS a) -> [a]
treeWToList (NodeW NilS V0) = []
treeWToList (NodeW (ConsS x) (V1 xs)) = x : treeWToList xs
-- ****    Strongly Typed AG Implementation
-- page 101
{-
type AG c i s = forall p . c p -> (i, p s) -> (s, p i)
-}
-- page 101
{-
runAG :: Shape c =>  AG c i s  ->  TreeW c (i -> s)
runAG g (NodeW c tt) i = s
  where (s , ii) = g c (i, ss)
        ss = liftA2 (runAG g) tt ii
-}
-- ****    ListAG
-- page 102
{-
data ListAG a i s = ListAG (i -> s) (a -> s -> i -> (s, i))
-}
-- page 102
{-
fromListAG :: ListAG a i s -> AG (ListS a) i s
fromListAG (ListAG nil cons) NilS (i, V0) = (nil i, V0)
fromListAG (ListAG nil cons) (ConsS x) (i, V1 s) = (s', V1 i')
  where (s', i') = cons x s i
-}
-- page 102
{-
toListAG :: AG (ListS a) i s -> ListAG a i s
toListAG g = ListAG (nil g) (cons g)
 where nil g i = fst $ g NilS (i, V0)
       cons g x s i = (s',i')
         where (s', V1 i') = g (ConsS x) (i, V1 s)   
-}
-- ****    Attribute Grammar Systems
-- * 7.3 Containers and W Types
-- **  Type-Theoretical Implementation
-- page 103
{-
Container : Set₁ where
  _◁_ : (S : Set) -> (P : S -> Set) -> Container
-}
-- page 103
{-
⟦S ◁ P⟧ X = Σ(s:S)(P s -> X)
-}
-- page 103
{-
⟦S ◁ P⟧ g = \ (s , f) -> (s , g ∘ f)
-}
-- ****    Well-Orders
-- **  Haskell implementation
-- ****    Display Maps
-- ****    Type Families are the Display Maps of GADTS
-- page 105
data Dsum a where
  Dpair :: a b -> b -> Dsum a
-- page 105
newtype Dprod a = Dprod (forall b . a b -> b)
-- page 105
infix 0 :< 
data Ext s x where
  (:<) :: s p -> (p -> x) -> Ext s x
-- page 105
{-
data Ext s x where
  (:<) :: s f -> f x -> Ext s x
-}
-- page 105
{-
data Ext s x where
  (:<) :: s n -> Vec n x -> Ext s x
-}
-- page 105
data Vec n x where
  VNil :: Vec Zero x
  VCons :: x -> Vec n x -> Vec (Succ n) x
-- page 105
data Zero
data Succ n
-- * 7.4 Circular Programs as Compositions of AGs
-- ****    Overview
-- **  Generic View as a W Type
-- ****    W Types
-- page 106
data W s where
  Sup :: s p -> p (W s) -> W s
-- ****    Container Functor
-- page 106
data WF s x where
  WF :: s p -> p x -> WF s x
-- ****    Payload Functors
-- page 106
class Shape s where
  pureS :: s p -> x -> p x
  appS  :: s p -> p (x -> y) -> p x -> p y

instance Shape (ListS a) where
  pureS NilS = \case{}
  appS (ConsS h) (V1 f) (V1 x) = V1 (f x)
  
-- page 106
mapS :: Shape s => s p -> (x -> y) -> p x -> p y
mapS sp f px = appS sp (pureS sp f) px
-- page 106
instance Shape s => Functor (WF s) where
  fmap f (WF s p) = WF s (mapS s f p)
-- ****    Generic View as W Type
-- page 106
class (Shape s, Fix (WF s) t) => FixW s t | t -> s where -- no new method
-- page 106
instance Fix (WF (ListS a)) [a] where
  out [] = WF NilS V0
  out (h:t) = WF (ConsS h) (V1 t)
  inn (WF NilS V0) = []
  inn (WF (ConsS h) (V1 t)) = h:t
-- page 106
instance FixW (ListS a) [a] where
-- ****    Container Algebras
-- page 106
type AlgW s x = forall p . s p -> p x -> x
-- page 106
uncurryW :: AlgW s x -> Alg (WF s) x
curryW :: Alg (WF s) x -> AlgW s x
-- page 106
uncurryW f (WF s p) = f s p
curryW f s p = f (WF s p)
-- page 107
cataW :: (FixW s t) => AlgW s r -> t -> r
cataW = cata . uncurryW
-- -- ****    Compatibility with Fix
-- **  Generic AG Traversals
-- page 107
newtype AG f i s = AG {appAG :: forall p . f p -> (i , p s) -> (s , p i)}
-- page 107
algAG :: Shape f => AG f i s -> AlgW f (i -> s)
algAG (AG ag) f p i = s
  where  (s , pi) = ag f (i, appS f p pi)
-- ****    Remarks
-- page 107
runAG :: FixW f t => AG f i s -> t -> i -> s
runAG ag t i = cataW (algAG ag) t i
-- ****    Product of AG
-- page 107
{-
runAG (pairAG g1 g2) t (i1,i2) == (runAG g1 t i1, runAG g t i2)
-}
-- page 107
{-
algAG (pairAG g1 g2) == hpair (algAG g1) (algAG g2)
-}
-- page 107
pairAG :: Shape f => AG f a b -> AG f c d -> AG f (a,c) (b,d)
pairAG g1 g2 = AG $ \ f ~((a,c), pbd) -> 
  let (b, pa) = appAG g1 f (a, pb)
      (d, pc) = appAG g2 f (c, pd)
      pb      = mapS f fst pbd  -- "b" attributes from "(a,b)"
      pd      = mapS f snd pbd  -- "d" attributes from "(b,d)"
      pac     = mapS f (,) pa <*> pc -- pairs of "a" and "c" attributes
      (<*>)     = appS f
  in ((b,d), pac)
-- ****    Constant Inherited Attribute
-- page 107
inherit :: Shape f => (a -> AG f b c) -> AG f (a,b) c
inherit pag = AG $ \f ~((a,b), pc) ->
  let (c, pb) = appAG (pag a) f (b, pc)
  in (c, mapS f (\b -> (a,b)) pb)
-- ****    AG from an Algebras
-- page 107
synth :: Shape f => AlgW f s -> AG f () s
synth alg = AG $ \f ~((),s) -> (alg f s, pureS f ())
-- page 107
{-
algAG (synth (curryW alg)) == curryW (cons . alg . fmap ($ ()))
-}
-- page 107
{-
AlgW f (i -> s) -> AG f i s
-}
-- ****    Identity AG
-- page 107
{-
runAG idAG t == id
-}
-- page 107
idAG :: Shape f => AG f x x
idAG = AG $ \f ~(x, ps) -> (x, pureS f x)
-- **  ArrowAG
-- page 107
class (ArrowCata (WF f) h) => ArrowAG f h | h -> f where
  apply_ag :: (AG f i s, i) -h~> s
-- page 107
ag :: ArrowAG f h => AG f i s -> i -h~> s
ag g = proc i -> apply_ag -< (g,i)
-- page 107
ag_init :: ArrowAG f t => i -> t (AG f i s) s
ag_init i = proc g -> apply_ag -< (g,i)
-- **  Multiple Traversals
-- page 107
instance (FixW f t, Shape f) => ArrowAG f (Env t) where
  apply_ag = Env $ \t (g,i) -> runAG g t i
-- **  Circular Implementation
-- page 107
data CircAG f a b  =  forall i s . CAG (a -> s -> (AG f i s, i, b))
-- ****    Running the Circular Computation
-- page 107
circAGtoEnv :: FixW f t => CircAG f a b -> Env t a b
circAGtoEnv = Env . runCircAG
runCircAG :: FixW f t => CircAG f a b -> t -> a -> b
runCircAG (CAG body) struct param = result
  where (ag, inherited, result) = body param (runAG ag struct inherited)
-- ****    Instances Definitions
-- page 107
instance Shape f => Category (CircAG f) where
  id = arr id
  CAG b2 . CAG b1 =  CAG $ \ x ~(s1 , s2) -> -- the lazy pattern is crucial
    let (g1, i1, r1) = b1 x s1
        (g2, i2, r2) = b2 r1 s2
    in (pairAG g1 g2, (i1, i2), r2)
-- page 111
instance Shape f => Arrow (CircAG f) where
  arr f = CAG $ \x ~() -> (idAG, (), f x) -- arr :: (a -> b) -> (a -h~> b)
  first (CAG b) = CAG $ \(x,y) s -> -- first :: (a -h~> b) -> ((a,c) -h~> (b,c))
    let (g, i, r) = b x s
     in (g, i, (r,y))
-- page 111
instance Shape f => ArrowCata (WF f) (CircAG f) where
  cataA = ag_init () <<< arr (\x -> synth (curryW x)) -- cataA :: Alg (WF f) x -h~> x
-- page 111
instance Shape f => ArrowAG f (CircAG f) where
  apply_ag = CAG $ \ ~(g,i) s -> (g, i, s) -- apply_ag :: (AG f i s, i) -h~> s
-- page 111
instance Shape f => ArrowLoop (CircAG f) where 
  loop (CAG b) = CAG $ \ x s -> -- loop :: ((a, r) -h~> (b, r)) -> (a -h~> b)
    let (g, i, ~(y, r)) = b (x, r) s
     in (g, i, y)
-- * 7.5 Examples
-- **  Palindrome
-- page 111
eqlistAG :: Eq a => AG (ListS a) [a] Bool
eqlistAG = AG $ \case
  NilS    -> \(y, V0)   -> (null y, V0)
  ConsS a -> \(y, V1 t) -> case y of
    [] -> (False, V1 [])
    (x:y') -> (a == x && t, V1 y')
-- page 112
eqlistA :: (Eq a, ArrowAG (ListS a) h) => [a] -h~> Bool
eqlistA = ag eqlistAG
-- page 112
revcatAG :: AG (ListS a) [a] [a]
revcatAG = AG $ \case
  NilS    -> \(z, V0)   -> (z, V0)
  ConsS a -> \(z, V1 r) -> (r, V1 (a:z))
-- page 112
reverseA :: ArrowAG (ListS a) h => () -h~> [a]
reverseA = proc () -> ag revcatAG -< []
-- page 112
palindromeA2 :: (Eq a, ArrowAG (ListS a) h) => () -h~> Bool
palindromeA2 = eqlistA . reverseA
-- page 112
palindrome6 :: (Eq a) => [a] -> Bool
palindrome6 x = runCircAG palindromeA2 x ()
-- ***   Removing the Redundant Tests
-- page 112
palindrome7 x = equalprefix (n + q) x (reverse x)
  where (n, q) = length x `quotRem` 2
-- page 112
equalprefix n x y
  | n <= 0 = True
  | null x || null y = False
  | otherwise = head x == head y 
              && equalprefix (n - 1) (tail x) (tail y)
-- page 113
listAlgW :: b -> (a -> b -> b) -> AlgW (ListS a) b
listAlgW n c NilS V0 = n
listAlgW n c (ConsS x) (V1 xs) = c x xs
-- page 113
lengthAlgW :: AlgW (ListS a) Int
lengthAlgW = listAlgW 0 ((+) . const 1)
-- page 113
lengthA2 :: ArrowAG (ListS a) h => () -h~> Int
lengthA2 = ag (synth lengthAlgW)
-- page 113
equalprefixAG :: Eq a => AG (ListS a) (Int, [a]) Bool
equalprefixAG = AG $ \case
  NilS -> \ ((n,y), V0) -> (n <= 0, V0)
  ConsS a -> \ ((n,y), V1 t) ->
    if n <= 0 then (True, V1 (n,y))
    else case y of [] -> (False, V1 (n,y))
                   (b:y') -> (a == b && t, V1 (n-1, y'))
-- page 113
equalprefixA :: (Eq a, ArrowAG (ListS a) h) => (Int, [a]) -h~> Bool
equalprefixA = ag equalprefixAG
-- page 113
palindrome8 = proc () -> do
  rev <- reverseA -< ()
  len <- lengthA2 -< ()
  let (n, q) = len `quotRem` 2
  equalprefixA -< (n + q, rev)
