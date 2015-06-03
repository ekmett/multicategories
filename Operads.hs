{-# LANGUAGE TypeOperators, KindSignatures, DataKinds, TypeFamilies, GADTs, RankNTypes, DeriveFunctor #-}
import Control.Comonad
import Data.Constraint
import Data.Semigroupoid

data Nat = Z | S Nat

type family (a :: Nat) + (b :: Nat) :: Nat
type instance Z   + m = m
type instance S n + m = S (n + m)

plus0 :: Dict ((n + Z) ~ n)
plus0 = undefined

plusAssoc :: p a -> q b -> r c -> Dict (((a + b) + c) ~ (a + (b + c)))
plusAssoc = undefined

data Vec n a where
  VCons :: a -> Vec n a -> Vec (S n) a
  VNil :: Vec Z a

instance Functor (Vec n) where
  fmap f (VCons a as) = VCons (f a) (fmap f as)
  fmap _ VNil = VNil

data Forest f n m where
  Nil :: Forest f Z Z 
  Cons :: f n -> Forest f i o -> Forest f (n + i) (S o)

instance Operad f => Semigroupoid (Forest f)

class Operad (f :: Nat -> *) where
  ident :: f (S Z)
  compose :: f n -> Forest f m n -> f m
  
data M f a where
   M :: f n -> Vec n a -> M f a

type OperadAlgebra f a = M f a -> a
type OperadCoalgebra f a = a -> M f a

newtype W f a = W { runW :: forall n. f n -> Vec n a }

instance Functor (W f) where

instance Operad f => Comonad (W f) where
  extract (W k) = case k ident of
    VCons a VNil -> a


