{-# LANGUAGE DataKinds, RankNTypes, TypeOperators, KindSignatures, GADTs, ScopedTypeVariables, PolyKinds, TypeFamilies #-}
module Multicategories where

import Control.Applicative
import Control.Category
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

class Graded f where
  grade :: f is o -> Rec Proxy is

class KnownGrade is where
  gradeVal :: Rec Proxy is

instance KnownGrade '[] where
  gradeVal = RNil

instance KnownGrade is => KnownGrade (i ': is) where
  gradeVal = Proxy :& gradeVal

data Args :: ([k] -> k -> *) -> [k] -> [k] -> * where
  Nil  :: Args f '[] '[]
  (:-) :: f i o -> Args f is os -> Args f (i ++ is) (o ': os)

infixr 5 :-

foldrArgs :: (forall i o is os. f i o -> r is os -> r (i ++ is) (o ': os)) -> r '[] '[] -> Args f m n -> r m n
foldrArgs _ z Nil = z
foldrArgs f z (a :- as) = f a (foldrArgs f z as)

data Grade is os = Grade { degrade :: Rec Proxy is }

gradeArgs :: Graded f => Args f is os -> Rec Proxy is
gradeArgs as = degrade $ foldrArgs (\a (Grade r) -> Grade $ grade a `rappend` r) (Grade RNil) as

-- | multicategory / planar colored operad
class Graded f => Multicategory f where
  ident   :: f '[a] a
  compose :: f bs c -> Args f as bs -> f as c

-- | generators for the symmetric groupoid Sigma_k
data Swap :: [a] -> [a] -> * where
  Swap :: Swap (a ': b ': as) (a ': b ': bs)
  Skip :: Swap as bs -> Swap (a ': as) (a ': bs)

class Multicategory f => Symmetric f where
  swap :: Swap as bs -> f as o -> f bs o

-- | The endomorphism multicategory over a Hask
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

-- polykinded Const
newtype K a b = K a

-- the monad associated with an operad
data M (f :: [()] -> () -> *) (a :: *) where
  M :: f is '() -> Rec (K a) is -> M f a

-- instance Multicategory f => Monad (M f)

-- a mcbride-style indexed monad associated with a multicategory
data IM (f :: [k] -> k -> *) (a :: k -> *) (o :: k) where
  IM :: f is o -> Rec a is -> IM f a o

-- | One category you get when given an operad. This is a forgetful functor that forgets all but the unary arrows.
newtype Oper f a b = Oper { runOper :: f '[a] b }

opermap :: (forall as b. f as b -> g as b) -> Oper f a b -> Oper g a b
opermap f (Oper a) = Oper (f a)

instance Multicategory f => Category (Oper f) where
  id = Oper ident
  Oper f . Oper g = Oper $ compose f (g :- Nil)

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
