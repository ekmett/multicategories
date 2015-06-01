{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Multicategories where

import Control.Applicative hiding (Const(..))
import Control.Category
import Control.Comonad
import Control.Monad (ap)
import Control.Monad.ST
import Data.Constraint
import Data.Foldable
import Data.Functor.Identity
import Data.Functor.Rep
import Data.Groupoid
import Data.Monoid (Monoid(..), (<>))
import Data.Proxy
import Data.Semigroupoid
import Data.Semigroupoid.Ob
import Data.Traversable
import Data.Type.Equality
import GHC.TypeLits
import Unsafe.Coerce
import Prelude hiding ((++), id, (.))

--------------------------------------------------------------------------------
-- * Coloured PROs
--------------------------------------------------------------------------------

-- | The is really talking about a Category, where @Ob f@ describes the objects.
--
-- We can also have multiple objects, so this is really a Coloured PRO.
--
-- The case where k = () is a normal PRO

class Semigroupoid p => PRO (p :: [k] -> [k] -> *) where
  pro :: p as bs -> p cs ds -> p (as ++ cs) (bs ++ ds)

--------------------------------------------------------------------------------
-- * (Erasable) Type-Level Lists
--------------------------------------------------------------------------------

type family (++) (a :: [k]) (b :: [k]) :: [k]
type instance '[] ++ bs = bs
type instance (a ': as) ++ bs = a ': (as ++ bs)

-- | Proof provided by every single class on theorem proving in the last 20 years.
appendNilAxiom :: forall as. Dict (as ~ (as ++ '[]))
appendNilAxiom = unsafeCoerce (Dict :: Dict (as ~ as))

-- | Proof provided by every single class on theorem proving in the last 20 years.
appendAssocAxiom :: forall p q r as bs cs. p as -> q bs -> r cs -> Dict ((as ++ (bs ++ cs)) ~ ((as ++ bs) ++ cs))
appendAssocAxiom _ _ _ = unsafeCoerce (Dict :: Dict (as ~ as))

--------------------------------------------------------------------------------
-- * Records
--------------------------------------------------------------------------------

-- | Note: @Rec Proxy is@ is a natural number we can do induction on.
data Rec :: (k -> *) -> [k] -> * where
  RNil :: Rec f '[]
  (:&) :: !(f a) -> !(Rec f as) -> Rec f (a ': as)

-- | Append two records
rappend :: Rec f as -> Rec f bs -> Rec f (as ++ bs)
rappend RNil bs      = bs
rappend (a :& as) bs = a :& rappend as bs

-- | Map over a record
rmap :: (forall a. f a -> g a) -> Rec f as -> Rec g as
rmap _ RNil = RNil
rmap f (a :& as) = f a :& rmap f as

-- | Split a record
splitRec :: Rec f is -> Rec g (is ++ js) -> (Rec g is, Rec g js)
splitRec RNil    as        = (RNil, as)
splitRec (_ :& is) (a :& as) = case splitRec is as of
  (l,r) -> (a :& l, r)

splitRec' :: Rec f is -> Rec f js -> Rec g (is ++ js) -> (Rec g is, Rec g js)
splitRec' RNil      js as        = (RNil, as)
splitRec' (_ :& is) js (a :& as) = case splitRec' is js as of
  (l,r) -> (a :& l, r)

foldrRec :: (forall i is. f i -> r is -> r (i ': is)) -> r '[] -> Rec f is -> r is
foldrRec _ z RNil = z
foldrRec f z (a :& as) = f a (foldrRec f z as)

traverseRec :: Applicative m => (forall i. f i -> m (g i)) -> Rec f is -> m (Rec g is)
traverseRec f (a :& as) = (:&) <$> f a <*> traverseRec f as
traverseRec f RNil = pure RNil

--------------------------------------------------------------------------------
-- * Graded structures
--------------------------------------------------------------------------------

class Graded (f :: [i] -> j -> *) where
  grade :: f is o -> Rec Proxy is
  {-# MINIMAL grade #-}

class KnownGrade is where
  gradeVal :: Rec Proxy is
  {-# MINIMAL gradeVal #-}

instance KnownGrade '[] where
  gradeVal = RNil

instance KnownGrade is => KnownGrade (i ': is) where
  gradeVal = Proxy :& gradeVal

--------------------------------------------------------------------------------
-- * Arguments for a multicategory form a polycategory
--------------------------------------------------------------------------------

-- | Each 'Multicategory' is a contravariant functor in @'Forest' f@ in its first argument.
data Forest :: ([k] -> k -> *) -> [k] -> [k] -> * where
  Nil  :: Forest f '[] '[]
  (:-) :: f is o -> Forest f js os -> Forest f (is ++ js) (o ': os)

infixr 5 :-, :&

foldrForest :: (forall i o is. f i o -> r is -> r (i ++ is)) -> r '[] -> Forest f m n -> r m
foldrForest _ z Nil = z
foldrForest f z (a :- as) = f a (foldrForest f z as)

instance Graded f => Graded (Forest f) where
  grade = foldrForest (\a r -> grade a `rappend` r) RNil

splitForest :: forall f g ds is js os r. Rec f is -> Forest g js os -> Forest g ds (is ++ js) -> (forall bs cs. (ds ~ (bs ++ cs)) => Forest g bs is -> Forest g cs js -> r) -> r
splitForest RNil bs as k = k Nil as
splitForest (i :& is) bs ((j :: g as o) :- js) k = splitForest is bs js $ \ (l :: Forest g bs as1) (r :: Forest g cs js) ->
  case appendAssocAxiom (Proxy :: Proxy as) (Proxy :: Proxy bs) (Proxy :: Proxy cs) of
    Dict -> k (j :- l) r

--------------------------------------------------------------------------------
-- * Multicategories
--------------------------------------------------------------------------------

-- | multicategory / planar colored operad
class Graded f => Multicategory f where
  ident   :: f '[a] a
  compose :: f bs c -> Forest f as bs -> f as c
  {-# MINIMAL ident, compose #-}

instance Multicategory f => Semigroupoid (Forest f) where
  o Nil Nil = Nil
  o (b :- bs) as = splitForest (grade b) bs as $ \es fs -> compose b es :- o bs fs

instance (Multicategory f, KnownGrade is) => Ob (Forest f) is where
  semiid = idents gradeVal

instance Multicategory f => PRO (Forest f) where
  pro Nil rs = rs
  pro (l :- ls) rs = case appendAssocAxiom (grade l) (grade ls) (grade rs) of
    Dict -> l :- pro ls rs

idents :: Multicategory f => Rec Proxy is -> Forest f is is
idents (a :& as) = ident :- idents as
idents RNil      = Nil

--------------------------------------------------------------------------------
-- * Symmetric Multicategories
--------------------------------------------------------------------------------

-- | generators for the symmetric groupoid Sigma_k
data Swap :: [a] -> [a] -> * where
  Swap :: Swap (a ': b ': bs) (b ': a ': bs)
  Skip :: Swap as bs -> Swap (a ': as) (a ': bs)

flop :: Swap as bs -> Swap bs as
flop Swap = Swap
flop (Skip as) = Skip (flop as)

swapRec :: Swap as bs -> Rec f as -> Rec f bs
swapRec (Skip s) (i :& is)      = i :& swapRec s is
swapRec Swap     (i :& j :& is) = j :& i :& is

unswapRec :: Swap bs as -> Rec f as -> Rec f bs
unswapRec (Skip s) (i :& is)      = i :& unswapRec s is
unswapRec Swap     (i :& j :& is) = j :& i :& is

class Multicategory f => Symmetric f where
  swap :: Swap as bs -> f as o -> f bs o
  {-# MINIMAL swap #-}

data Coselector a as bs where
  Cohead :: Rec Proxy as -> Coselector a (a ': as) as
  Cotail :: Coselector a as bs -> Coselector a (b ': as) (b ': bs)

-- The symmetric groupoid
data Sigma as bs where
  SNil :: Sigma '[] '[]
  SCons :: Coselector a as bs -> Sigma as bs -> Sigma as (a ': bs)

instance Semigroupoid Sigma
instance Groupoid Sigma
instance PRO Sigma
instance PROP Sigma
instance KnownGrade as => Ob Sigma as
  
--------------------------------------------------------------------------------
-- * Coloured PROPs
--------------------------------------------------------------------------------

class PRO p => PROP p where
  prop :: Swap as bs -> p as bs

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
  compose (Endo _ f) as = Endo (grade as) $ \v -> f $ go as v where
    go :: Forest Endo is os -> Rec Identity is -> Rec Identity os
    go (Endo gg g :- gs) v = case splitRec gg v of
      (l,r) -> Identity (g l) :& go gs r
    go Nil RNil = RNil

instance Symmetric Endo where -- TODO
  swap s (Endo g f) = Endo (swapRec s g) (f . unswapRec s)

--------------------------------------------------------------------------------
-- * Free multicategory
--------------------------------------------------------------------------------

-- | free multicategory given graded atoms
data Free :: ([k] -> k -> *) -> [k] -> k -> * where
  Ident :: Free f '[a] a
  Apply :: f bs c -> Forest (Free f) as bs -> Free f as c

instance Graded f => Graded (Free f) where
  grade Ident = Proxy :& RNil
  grade (Apply _ as) = grade as

instance Graded f => Multicategory (Free f) where
  ident = Ident
  compose Ident ((a :: Free f bs c) :- Nil) = case appendNilAxiom :: Dict (bs ~ (bs ++ '[])) of Dict -> a
  compose (Apply f as) bs = Apply f (o as bs)

--------------------------------------------------------------------------------
-- * The monad attached to a planar operad
--------------------------------------------------------------------------------

data Atkey a i j where
  Atkey :: a -> Atkey a i i

amap :: (a -> b) -> Atkey a i j -> Atkey b i j
amap f (Atkey a) = Atkey (f a)

-- The monad attached to an operad. This generalizes the notion of the writer monad to an arbitrary operad
data M (f :: [()] -> () -> *) (a :: *) where
  M :: f is '() -> Rec (Atkey a '()) is -> M f a

instance Functor (M f) where
  fmap f (M s d) = M s (rmap (amap f) d)

instance Multicategory f => Applicative (M f) where
  pure = return
  (<*>) = ap

instance Multicategory f => Monad (M f) where
  return a = M ident (Atkey a :& RNil)
  M s0 d0 >>= (f :: a -> M f b) = go d0 $ \ as ds -> M (compose s0 as) ds where
    go :: Rec (Atkey a '()) is -> (forall os. Forest f os is -> Rec (Atkey b '()) os -> r) -> r
    go RNil k = k Nil RNil
    go (Atkey a :& is) k = go is $ \fs as -> case f a of
      M s bs -> k (s :- fs) (rappend bs as)

instance Foldable (M f) where
  foldr f z (M _ d) = getConst $ foldrRec (\(Atkey a) (Const b) -> Const (f a b)) (Const z) d

instance Traversable (M f) where
  traverse f (M s d) = M s <$> traverseRec (\(Atkey a) -> Atkey <$> f a) d

-- polykinded Const
newtype Const a b = Const { getConst :: a }

--------------------------------------------------------------------------------
-- * The monad transformer attached to a planar operad
--------------------------------------------------------------------------------

data T f g o where
  T :: f is o -> g is -> T f g o

-- This does not form a valid monad unless the monad @m@ is commutative. (Just like @ListT@)
newtype MT (f :: [()] -> () -> *) (m :: * -> *) (a :: *) = MT { runMT :: m (T f (Rec (Atkey a '())) '()) }

instance Functor m => Functor (MT f m) where
  fmap f (MT m) = MT $ fmap (\(T s d) -> T s (rmap (amap f) d)) m

instance (Multicategory f, Functor m, Monad m) => Applicative (MT f m) where
  pure = return
  (<*>) = ap

instance (Multicategory f, Monad m) => Monad (MT f m) where
  return a = MT (return (T ident (Atkey a :& RNil)))
  MT m >>= (f :: a -> MT f m b) = MT $ do
      T s0 d0 <- m
      go d0 $ \ as ds -> return $ T (compose s0 as) ds
    where
      go :: Rec (Atkey a '()) is -> (forall os. Forest f os is -> Rec (Atkey b '()) os -> m r) -> m r
      go RNil k = k Nil RNil
      go (Atkey a :& is) k = go is $ \fs as -> do
        T s bs <- runMT (f a)
        k (s :- fs) (rappend bs as)
  fail s = MT $ fail s

instance Foldable m => Foldable (MT f m) where
  foldr f z (MT m) = Data.Foldable.foldr (\(T _ d) z' -> getConst $ foldrRec (\(Atkey a) (Const r) -> Const (f a r)) (Const z') d) z m

instance Traversable m => Traversable (MT f m) where
  traverse f (MT m) = MT <$> traverse (\(T s d) -> T s <$> traverseRec (\(Atkey a) -> Atkey <$> f a) d) m

-- TODO: Build a monad transformer associated with an operad based on ListT-done-right?

--------------------------------------------------------------------------------
-- * Algebras over a Operad
--------------------------------------------------------------------------------

type OperadAlgebra f a = M f a -> a
type OperadCoalgebra f a = a -> M f a

--------------------------------------------------------------------------------
-- * Indexed Monads from a Multicategory
--------------------------------------------------------------------------------

type (f :: k -> *) ~> (g :: k -> *) = forall (a :: k). f a -> g a
infixr 0 ~>

class IFunctor m where
  imap :: (a ~> b) -> m a ~> m b
  {-# MINIMAL imap #-}

class IFunctor m => IMonad m where
  ireturn :: a ~> m a
  ibind :: (a ~> m b) -> (m a ~> m b)
  {-# MINIMAL ireturn, ibind #-}

-- | A McBride-style indexed monad associated with a multicategory
data IM (f :: [k] -> k -> *) (a :: k -> *) (o :: k) where
  IM :: f is o -> Rec a is -> IM f a o

instance IFunctor (IM f) where
  imap f (IM s d) = IM s (rmap f d)

instance Multicategory f => IMonad (IM f) where
  ireturn a = IM ident (a :& RNil)
  ibind (f :: a ~> IM f b) (IM s0 d0) = go d0 $ \ as ds -> IM (compose s0 as) ds where
    go :: Rec a is -> (forall os. Forest f os is -> Rec b os -> r) -> r
    go RNil k = k Nil RNil
    go (a :& is) k = go is $ \fs as -> case f a of
      IM s bs -> k (s :- fs) (rappend bs as)

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
  swap x = x `seq` error "The permutations of 1 element are trivial. How did you get here?"

--------------------------------------------------------------------------------
-- * Selectors
--------------------------------------------------------------------------------

data Selector :: [k] -> k -> * where
  Head :: Rec Proxy as  -> Selector (a ': as) a
  Tail :: Selector as b -> Selector (a ': as) b

selectors :: Rec f as -> Rec (Selector as) as
selectors RNil      = RNil
selectors (_ :& as) = Head (rmap (const Proxy) as) :& rmap Tail (selectors as)

-- @Rec f@ is represented by @Selector@
select :: Rec f is -> Selector is ~> f
select (a :& _) (Head _) = a
select (_ :& b) (Tail c) = select b c

tabulate :: KnownGrade is => (Selector is ~> f) -> Rec f is
tabulate f = rmap f (selectors gradeVal)

instance Graded Selector where
  grade (Tail as) = Proxy :& grade as
  grade (Head as) = Proxy :& as

instance Multicategory Selector where
  ident = Head RNil
  compose (Tail (as :: Selector os b)) (b :- (bs :: Forest Selector js os)) = go (grade b) where
    go :: Rec Proxy ks -> Selector (ks ++ js) b
    go RNil      = compose as bs
    go (c :& cs) = Tail (go cs)
  compose (Head (as :: Rec Proxy os)) ((b :: Selector is o) :- (bs :: Forest Selector js os)) = go b where
    go :: forall ks. Selector ks o -> Selector (ks ++ js) o
    go (Tail cs) = Tail (go cs)
    go (Head cs) = Head (rappend cs (grade bs))

instance Symmetric Selector where
  swap (Skip as) (Head bs)        = Head (swapRec as bs)
  swap Swap      (Head (_ :& bs)) = Tail (Head bs)
  swap (Skip as) (Tail bs)        = Tail (swap as bs)
  swap Swap      (Tail (Head bs)) = Head (Proxy :& bs)
  swap Swap      (Tail (Tail bs)) = Tail (Tail bs)

--------------------------------------------------------------------------------
-- * Cartesian Multicategories and Finite-Product Theories
--------------------------------------------------------------------------------

-- the theory of multisorted equality, acts as a sort of multisorted FinSet^op or multisorted FinBool

data Cart is os where
  Cart :: Rec Proxy is -> Rec (Selector is) os -> Cart is os

instance Semigroupoid Cart where
  Cart bs bcs `o` Cart as abs = Cart as (rmap (select abs) bcs)

instance KnownGrade is => Ob Cart is where
  semiid = Cart r (selectors r) where
    r = gradeVal

instance Graded Cart where
  grade (Cart g _) = g

class Symmetric f => Cartesian f where
  cart :: f bs c -> Cart as bs -> f as c
  {-# MINIMAL cart #-}

instance Cartesian Endo where
  cart (Endo gf f) (Cart gc c) = Endo gc $ \v -> f (rmap (select v) c)

instance Cartesian Selector where
  cart s (Cart _ r) = select r s

-- | Finite Product Theory -- Multisorted Lawvere Theory where the set of objects is all of Ob f itself
--
-- <http://ncatlab.org/nlab/show/Lawvere+theory>
class PROP p => ProductTheory p where
  prod :: Cart as bs -> p as bs

instance PRO Cart
instance PROP Cart
instance ProductTheory Cart

--------------------------------------------------------------------------------
-- * Variants
--------------------------------------------------------------------------------

data Variant :: (k -> *) -> [k] -> * where
  Variant :: Selector as a -> f a -> Variant f as

--------------------------------------------------------------------------------
-- * The comonad associated with an operad.
--------------------------------------------------------------------------------

newtype Coatkey a i j = Coatkey { getCoatkey :: (i ~ j) => a }

-- | The comonad associated with an operad
newtype W (f :: [()] -> () -> *) (a :: *) = W { runW :: forall is. f is '() -> Rec (Coatkey a '()) is }

instance Functor (W f) where
  fmap f (W g) = W (rmap (\(Coatkey a) -> Coatkey (f a)) . g)

instance Multicategory f => Comonad (W f) where
  extract (W f) = case f ident of
    Coatkey a :& RNil -> a
  extend (f :: W f a -> b) (w :: W f a) = W $ \s -> go RNil (grade s) s where
    go :: forall (ls :: [()]) (rs :: [()]). Rec Proxy ls -> Rec Proxy rs -> f (ls ++ rs) '() -> Rec (Coatkey b '()) rs
    go _ RNil _ = RNil
    go ls (p :& rs) s = g :& go (rappend ls (p :& RNil)) rs (shift s)
      where
        g = Coatkey $ f $ W $ \s' ->
          prune ls (grade s') rs (runW w (compose s (pro (idents ls) (s' :- idents rs))))
        prune ls is rs = fst . splitRec' is rs . snd . splitRec' ls (rappend is rs)
        shift s = case appendAssocAxiom ls (p :& RNil) rs of Dict -> s

--------------------------------------------------------------------------------
-- * Indexed Monads from a Multicategory
--------------------------------------------------------------------------------

-- instance Multicategory f => IMonad (IM f)

class IFunctor w => IComonad w where
  iextract :: w a ~> a
  iextend  :: (w a ~> b) -> (w a ~> w b)

-- an indexed comonad associated with a multicategory
newtype IW (f :: [k] -> k -> *) (a :: k -> *) (o :: k) = IW { runIW :: forall is. f is o -> Rec a is }

instance IFunctor (IW f) where
  imap f (IW g) = IW $ \s -> rmap f (g s)

instance Multicategory f => IComonad (IW f) where
  iextract (IW f) = case f ident of
    a :& RNil -> a
  iextend (f :: IW f a ~> b) (w :: IW f a o) = IW $ \s -> go RNil (grade s) s where
    go :: forall ls rs. Rec Proxy ls -> Rec Proxy rs -> f (ls ++ rs) o -> Rec b rs
    go _ RNil _ = RNil
    go ls (p :& rs) s = f g :& go (rappend ls (p :& RNil)) rs (shift s)
      where
        g = IW $ \s' -> prune ls (grade s') rs (runIW w (compose s (pro (idents ls) (s' :- idents rs))))
        prune ls is rs = fst . splitRec' is rs . snd . splitRec' ls (rappend is rs)
        shift s = case appendAssocAxiom ls (p :& RNil) rs of Dict -> s

--------------------------------------------------------------------------------
-- * A category over an operad
--------------------------------------------------------------------------------
-- TODO: http://ncatlab.org/nlab/show/category+over+an+operad

--------------------------------------------------------------------------------
-- * The operad associated with a monoid
--------------------------------------------------------------------------------

-- M (MonoidOp m) is isomorphic to Writer m, W (MonoidOp m) is isomorphic to Traced m
data MonoidOp m :: [()] -> () -> * where
  MonoidOp :: m -> MonoidOp m '[a] a

instance Graded (MonoidOp m) where
  grade MonoidOp{} = Proxy :& RNil

instance Monoid m => Multicategory (MonoidOp m) where
  ident = MonoidOp mempty
  compose (MonoidOp m1) (MonoidOp m2 :- Nil) = MonoidOp (m1 <> m2)

--------------------------------------------------------------------------------
-- * Natural numbers
--------------------------------------------------------------------------------


-- M N -- is the finite list monad
-- W N -- is the infinite stream comonad (Sum Natural -> a)

-- | natural number multicategory
data N :: [k] -> k -> * where
  N :: Rec ((:~:) i) is -> N is i

instance Graded N where
  grade (N as) = rmap (const Proxy) as

instance Multicategory N where
  ident = N (Refl :& RNil)

instance Symmetric N
instance Cartesian N

--------------------------------------------------------------------------------
-- * Core of a Category
--------------------------------------------------------------------------------

-- | The core of a category is the largest sub-groupoid
data Core p as bs = Core { hither :: p as bs, yon :: p bs as }

instance Semigroupoid p => Semigroupoid (Core p) where
  o (Core e f) (Core g h) = Core (o e g) (o h f)

instance Category p => Category (Core p) where
  id = Core id id
  Core e f . Core g h = Core (e . g) (h . f)

instance Ob p a => Ob (Core p) a where
  semiid = Core semiid semiid

instance Semigroupoid p => Groupoid (Core p) where
  inv (Core f g) = Core g f

instance PRO p => PRO (Core p) where
  pro (Core as bs) (Core cs ds) = Core (pro as cs) (pro bs ds)

instance PROP p => PROP (Core p) where
  prop s = Core (prop s) (prop (flop s))

-- the symmetric groupoid Sigma is the symmetric groupoid, the core of a coloured version of FinSet^op
type Sym = Core Cart
