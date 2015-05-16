{-# LANGUAGE DataKinds, RankNTypes, TypeOperators, KindSignatures, GADTs, ScopedTypeVariables, PolyKinds, TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}
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
import Data.Semigroupoid.Ob
import Data.Vector as Vector
import Data.Vector.Mutable as Mutable
import GHC.TypeLits
import Unsafe.Coerce
import Prelude hiding ((++), id, (.))

--------------------------------------------------------------------------------
-- * Records
--------------------------------------------------------------------------------

-- | Note: @Rec Proxy is@ is a natural number we can do induction on.
data Rec :: (k -> *) -> [k] -> * where
  RNil :: Rec f '[]
  (:&) :: !(f a) -> !(Rec f as) -> Rec f (a ': as)

type family (++) (a :: [k]) (b :: [k]) :: [k]
type instance '[] ++ bs = bs
type instance (a ': as) ++ bs = a ': (as ++ bs)

appendNilAxiom :: forall as. Dict (as ~ (as ++ '[]))
appendNilAxiom = unsafeCoerce (Dict :: Dict (as ~ as))

appendAssoc :: forall p q r as bs cs. p as -> q bs -> r cs -> Dict ((as ++ (bs ++ cs)) ~ ((as ++ bs) ++ cs))
appendAssoc _ _ _ = unsafeCoerce (Dict :: Dict (as ~ as))

rappend :: Rec f as -> Rec f bs -> Rec f (as ++ bs)
rappend RNil bs      = bs
rappend (a :& as) bs = a :& rappend as bs

rmap :: (forall a. f a -> g a) -> Rec f as -> Rec g as
rmap _ RNil = RNil
rmap f (a :& as) = f a :& rmap f as

splitRec :: Rec f is -> Rec g (is ++ js) -> (Rec g is, Rec g js)
splitRec RNil    as        = (RNil, as)
splitRec (_ :& is) (a :& as) = case splitRec is as of
  (l,r) -> (a :& l, r)

--------------------------------------------------------------------------------
-- * Variants
--------------------------------------------------------------------------------

data Variant :: (k -> *) -> [k] -> * where
  Variant :: Selector f as a -> Variant f as

data Selector :: (k -> *) -> [k] -> k -> * where
  Head :: f a -> Selector f (a ': as) a
  Tail :: Selector f as b -> Selector f (a ': as) b

selectors :: Rec f as -> Rec (Selector f as) as
selectors RNil      = RNil
selectors (a :& as) = Head a :& rmap Tail (selectors as)

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
  (:-) :: f is o -> Args f js os -> Args f (is ++ js) (o ': os)

splitArgs :: forall f g as is js os r. Rec f is -> Args g js os -> Args g as (is ++ js) -> (forall bs cs. (as ~ (bs ++ cs)) => Args g bs is -> Args g cs js -> r) -> r
splitArgs RNil bs as k = k Nil as
splitArgs (i :& is) bs ((j :: g is1 o) :- js) k = splitArgs is bs js $ \ (l :: Args g bs as1) (r :: Args g cs js) ->
  case appendAssoc (Proxy :: Proxy is1) (Proxy :: Proxy bs) (Proxy :: Proxy cs) of
    Dict -> k (j :- l) r

instance Multicategory f => Semigroupoid (Args f) where
  o Nil Nil = Nil
  o (b :- bs) as = splitArgs (grade b) bs as $ \es fs -> compose b es :- o bs fs

instance (Multicategory f, KnownGrade is) => Ob (Args f) is where
  semiid = idents gradeVal

idents :: Multicategory f => Rec Proxy is -> Args f is is
idents (a :& as) = ident :- idents as
idents RNil      = Nil

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
  compose Ident ((a :: Free f bs c) :- Nil) = case appendNilAxiom :: Dict (bs ~ (bs ++ '[])) of Dict -> a
  compose (Apply f as) bs = Apply f (o as bs)

-- each operad is a contravariant functor in (Args f) in its first argument, and covariant in (Op f) in its second

--------------------------------------------------------------------------------
-- * Kleisli arrows of outrageous fortune
--------------------------------------------------------------------------------

data Atkey a i j where
  Atkey :: a -> Atkey a i i

--------------------------------------------------------------------------------
-- * The monad attached to a planar operad
--------------------------------------------------------------------------------

-- The monad attached to an operad. This generalizes the notion of the writer monad to an arbitrary operad
data M (f :: [()] -> () -> *) (a :: *) where
  M :: f is '() -> Rec (Atkey a '()) is -> M f a

instance Functor (M f) where
  fmap f (M s d) = M s (rmap (\(Atkey a) -> Atkey (f a)) d)

instance Multicategory f => Applicative (M f) where
  pure = return
  (<*>) = ap

instance Multicategory f => Monad (M f) where
  return a = M ident (Atkey a :& RNil)
  M s0 d0 >>= (f :: a -> M f b) = go d0 $ \ as ds -> M (compose s0 as) ds where
    go :: Rec (Atkey a '()) is -> (forall os. Args f os is -> Rec (Atkey b '()) os -> r) -> r
    go RNil k = k Nil RNil
    go (Atkey a :& is) k = go is $ \fs as -> case f a of
      M s bs -> k (s :- fs) (rappend bs as)

--------------------------------------------------------------------------------
-- * Algebras over a Operad
--------------------------------------------------------------------------------

type OperadAlgebra f a = M f a -> a
type OperadCoalgebra f a = a -> M f a

--------------------------------------------------------------------------------
-- * The comonad associated with an operad.
--------------------------------------------------------------------------------

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

type (f :: k -> *) ~> (g :: k -> *) = forall (a :: k). f a -> g a
infixr 0 ~>

class IFunctor m where
  imap :: (a ~> b) -> m a ~> m b

class IFunctor m => IMonad m where
  ireturn :: a ~> m a
  ibind :: (a ~> m b) -> (m a ~> m b)

-- a mcbride-style indexed monad associated with a multicategory
data IM (f :: [k] -> k -> *) (a :: k -> *) (o :: k) where
  IM :: f is o -> Rec a is -> IM f a o

instance IFunctor (IM f) where
  imap f (IM s d) = IM s (rmap f d)

instance Multicategory f => IMonad (IM f) where
  ireturn a = IM ident (a :& RNil)
  ibind (f :: a ~> IM f b) (IM s0 d0) = go d0 $ \ as ds -> IM (compose s0 as) ds where
    go :: Rec a is -> (forall os. Args f os is -> Rec b os -> r) -> r
    go RNil k = k Nil RNil
    go (a :& is) k = go is $ \fs as -> case f a of
      IM s bs -> k (s :- fs) (rappend bs as)

-- instance Multicategory f => IMonad (IM f)

class IFunctor w => IComonad w where
  iextract :: w a ~> a
  iextend  :: (w a ~> b) -> (w a ~> w b)

-- an indexed comonad associated with a multicategory
newtype IW (f :: [k] -> k -> *) (a :: k -> *) (o :: k) = IW { runIW :: forall is. f is o -> Rec a is }

-- instance Multicategory f => IComonad (IW f)

instance IFunctor (IW f) where
  imap f (IW g) = IW $ \s -> rmap f (g s)

instance Multicategory f => IComonad (IW f) where
  iextract (IW f) = case f ident of
    a :& RNil -> a
  iextend (f :: IW f a ~> b) (IW w) = IW $ \s -> go (grade s) s where
    go :: Rec Proxy is -> f is a1 -> Rec b is
    go gs s = undefined
  -- duplicate (W f) = W (\s d -> rmap (\(Atkey a) -> W $ \s' d' -> graft d' in for the corresponding arg of s, then prune the result to that interval) d)

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

--------------------------------------------------------------------------------
-- * A category over an operad
--------------------------------------------------------------------------------
-- http://ncatlab.org/nlab/show/category+over+an+operad

-- we could model a category with object constraints with something simple like:

-- class (Semigroupoid q, Semigroupoid r) => Profunctor p q r | p -> q r where
--   dimap :: q a b -> r c d -> p b c -> p a d

-- class (Profunctor p (Args p) (Oper p), Graded p) => Multicategory p where ident :: p '[a] a ...
--
-- now 'compose' is an lmap.
