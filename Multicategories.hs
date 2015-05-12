{-# LANGUAGE DataKinds, RankNTypes, TypeOperators, KindSignatures, GADTs, ScopedTypeVariables, PolyKinds, TypeFamilies #-}
module Multicategories where

import Control.Applicative
import Control.Category
import Control.Comonad
import Control.Monad (ap)
import Control.Monad.ST
import Data.Constraint
import Data.Functor.Identity
import Data.Functor.Rep
import Data.Proxy
import Data.Semigroupoid
import Data.Vector as Vector
import Data.Vector.Mutable as Mutable
import GHC.TypeLits
import Unsafe.Coerce
import Prelude hiding ((++), id, (.))

--------------------------------------------------------------------------------
-- * Records
--------------------------------------------------------------------------------

-- | Note: @Rec Proxy is@ a natural number we can do induction on.
data Rec :: (k -> *) -> [k] -> * where
  RNil :: Rec f '[]
  (:&) :: !(f a) -> !(Rec f as) -> Rec f (a ': as)

type family (++) (a :: [k]) (b :: [k]) :: [k]
type instance '[] ++ bs = bs
type instance (a ': as) ++ bs = a ': (as ++ bs)

rappend :: Rec f as -> Rec f bs -> Rec f (as ++ bs)
rappend RNil bs      = bs
rappend (a :& as) bs = a :& rappend as bs

rmap :: (forall a. f a -> g a) -> Rec f as -> Rec g as
rmap _ RNil = RNil
rmap f (a :& as) = f a :& rmap f as

--------------------------------------------------------------------------------
-- * Variants
--------------------------------------------------------------------------------

data Variant :: (k -> *) -> [k] -> * where
  Head :: f a -> Variant f (a ': as)
  Tail :: Variant f as -> Variant f (a ': as)

--------------------------------------------------------------------------------
-- * Graded structures
--------------------------------------------------------------------------------

class Graded f where
  grade :: f is o -> Rec Proxy is

class KnownGrade is where
  gradeVal :: Rec Proxy is

instance KnownGrade '[] where
  gradeVal = RNil

instance KnownGrade is => KnownGrade (i ': is) where
  gradeVal = Proxy :& gradeVal

--------------------------------------------------------------------------------
-- * Arguments for a multicategory form a polycategory
--------------------------------------------------------------------------------

data Args :: ([k] -> k -> *) -> [k] -> [k] -> * where
  Nil  :: Args f '[] '[]
  (:-) :: f i o -> Args f is os -> Args f (i ++ is) (o ': os)

infixr 5 :-

foldrArgs :: (forall i o is. f i o -> r is -> r (i ++ is)) -> r '[] -> Args f m n -> r m
foldrArgs _ z Nil = z
foldrArgs f z (a :- as) = f a (foldrArgs f z as)

gradeArgs :: Graded f => Args f is os -> Rec Proxy is
gradeArgs = foldrArgs (\a r -> grade a `rappend` r) RNil

--------------------------------------------------------------------------------
-- * Multicategories
--------------------------------------------------------------------------------

-- | multicategory / planar colored operad
class Graded f => Multicategory f where
  ident   :: f '[a] a
  compose :: f bs c -> Args f as bs -> f as c

--------------------------------------------------------------------------------
-- * Symmetric Multicategories
--------------------------------------------------------------------------------

-- | generators for the symmetric groupoid Sigma_k
data Swap :: [a] -> [a] -> * where
  Swap :: Swap (a ': b ': as) (a ': b ': bs)
  Skip :: Swap as bs -> Swap (a ': as) (a ': bs)

class Multicategory f => Symmetric f where
  swap :: Swap as bs -> f as o -> f bs o

-- TODO: Cartesian Multicategories

--------------------------------------------------------------------------------
-- * Endo
--------------------------------------------------------------------------------

-- | The endomorphism multicategory over a Hask; the multicategory represented by Hask.
data Endo is o where
  Endo :: !(Rec Proxy is) -> (Rec Identity is -> o) -> Endo is o

instance Graded Endo where
  grade (Endo g _) = g

splitRec :: Rec f is -> Rec g (is ++ js) -> (Rec g is, Rec g js)
splitRec RNil    as        = (RNil, as)
splitRec (_ :& is) (a :& as) = case splitRec is as of
  (l,r) -> (a :& l, r)

instance Multicategory Endo where
  ident = Endo gradeVal $ \(Identity a :& RNil) -> a
  compose (Endo _ f) as = Endo (gradeArgs as) $ \v -> f $ go as v where
    go :: Args Endo is os -> Rec Identity is -> Rec Identity os
    go (Endo gg g :- gs) v = case splitRec gg v of
      (l,r) -> Identity (g l) :& go gs r
    go Nil RNil = RNil

instance Symmetric Endo -- TODO

--------------------------------------------------------------------------------
-- * Free multicategory
--------------------------------------------------------------------------------

-- | free multicategory given graded atoms
data Free :: ([k] -> k -> *) -> [k] -> k -> * where
  Ident :: Free f '[a] a
  Apply :: f bs c -> Args (Free f) as bs -> Free f as c
  
instance Graded f => Graded (Free f) where
  grade Ident = Proxy :& RNil
  grade (Apply _ as) = gradeArgs as

instance Graded f => Multicategory (Free f) where
  ident = Ident
  compose Ident (a :- Nil) = unsafeCoerce a -- TODO: fix
  compose (Apply f0 as0) bs0 = Apply f0 $ go as0 bs0 where
    go :: Args (Free f) bs cs -> Args (Free f) as bs -> Args (Free f) as cs
    go (f :- fs) as = error "TODO"

-- each operad is a contravariant functor in (Args f) in its first argument, and covariant in (Op f) in its second

--------------------------------------------------------------------------------
-- * Kleisli arrows of outrageous fortune
--------------------------------------------------------------------------------

data Atkey a i j where
  Atkey :: a -> Atkey a i i
 
--------------------------------------------------------------------------------
-- * (Co)monads from a planar operad
--------------------------------------------------------------------------------

-- The monad associated with an operad. This generalizes the notion of the writer monad to an arbitrary operad
data M (f :: [()] -> () -> *) (a :: *) where
  M :: f is '() -> Rec (Atkey a '()) is -> M f a

instance Functor (M f) where
  fmap f (M s d) = M s (rmap (\(Atkey a) -> Atkey (f a)) d)

instance Multicategory f => Applicative (M f) where
  pure = return
  (<*>) = ap

instance Multicategory f => Monad (M f) where
  return a = M ident (Atkey a :& RNil)
  (>>=) = bind where
    bind :: forall a b. M f a -> (a -> M f b) -> M f b
    bind (M s0 d0) f = go d0 $ \ as ds -> M (compose s0 as) ds where
      go :: Rec (Atkey a '()) is -> (forall os. Args f os is -> Rec (Atkey b '()) os -> r) -> r
      go RNil k = k Nil RNil
      go (Atkey a :& is) k = go is $ \fs as -> case f a of
        M s bs -> k (s :- fs) (rappend bs as)

-- The comonad associated with an operad
newtype W (f :: [()] -> () -> *) (a :: *) = W { runW :: forall is. f is '() -> Rec (Atkey a '()) is } -- Coatkey?

instance Functor (W f) where
  fmap f (W g) = W (rmap (\(Atkey a) -> Atkey (f a)) . g)

instance Multicategory f => Comonad (W f) where
  extract (W f) = case f ident of
    Atkey a :& RNil -> a

--------------------------------------------------------------------------------
-- * Indexed (Co)monads from a Multicategory
--------------------------------------------------------------------------------

-- a mcbride-style indexed monad associated with a multicategory
data IM (f :: [k] -> k -> *) (a :: k -> *) (o :: k) where
  IM :: f is o -> Rec a is -> IM f a o

-- instance Multicategory f => IMonad (IM f)

-- an indexed comonad associated with a multicategory
newtype IW (f :: [k] -> k -> *) (a :: k -> *) (o :: k) = IW { runIW :: forall is. f is o -> Rec a is }

-- instance Multicategory f => IComonad (IW f)

--------------------------------------------------------------------------------
-- * A category obtained by keeping only 1-argument multimorphisms
--------------------------------------------------------------------------------

-- | One category you get when given an operad. This is a forgetful functor that forgets all but the unary arrows.
newtype Oper f a b = Oper { runOper :: f '[a] b }

opermap :: (forall as b. f as b -> g as b) -> Oper f a b -> Oper g a b
opermap f (Oper a) = Oper (f a)

instance Multicategory f => Category (Oper f) where
  id = Oper ident
  Oper f . Oper g = Oper $ compose f (g :- Nil)

--------------------------------------------------------------------------------
-- * Free multicategory from a category
--------------------------------------------------------------------------------

-- | Build a free multicategory from a category, left adjoint to Oper
data C :: (i -> i -> *) -> [i] -> i -> * where
  C :: p a b -> C p '[a] b

instance Graded (C p) where
  grade C{} = gradeVal

instance Category p => Multicategory (C p) where
  ident = C id
  compose (C f) (C g :- Nil) = C (f . g)

instance Category p => Symmetric (C p) where
  swap = error "The permutations of 1 element are trivial. How did you get here?"

-- we could model a category with object constraints with something simple like:

-- class (Semigroupoid q, Semigroupoid r) => Profunctor p q r | p -> q r where
--   dimap :: q a b -> r c d -> p b c -> p a d

-- class (Profunctor p (Args p) (Oper p), Graded p) => Multicategory p where ident :: p '[a] a ...
--
-- now 'compose' is an lmap.
