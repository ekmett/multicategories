{-# LANGUAGE PolyKinds, DataKinds, ConstraintKinds, TypeOperators, TypeFamilies, GADTs #-}

import Data.Proxy

data Player = X | O

data STATE = State [Maybe Player] Player

type family Other (p :: Player) :: Player where
  Other X = O
  Other O = X

type family Cons (a :: Maybe Player) (s :: STATE) where
  Cons a (State as x) = State (a ': as) x

type family MapCons (a :: Maybe Player) (ys :: [STATE]) where
  MapCons a (s ': bs) = Cons a s ': MapCons a bs
  MapCons a '[] = '[]

type family Won (b :: STATE) where
  Won (State '[Just X,Just X,Just X,a,b,c,d,e,f] O) = True
  Won (State '[a,b,c,Just X,Just X,Just X,d,e,f] O) = True
  Won (State '[a,b,c,d,e,f,Just X,Just X,Just X] O) = True
  Won (State '[Just X,a,b,Just X,c,d,Just X,e,f] O) = True
  Won (State '[a,Just X,b,c,Just X,d,e,Just X,f] O) = True
  Won (State '[a,b,Just X,c,d,Just X,e,f,Just X] O) = True
  Won (State '[Just X,a,b,c,Just X,d,e,f,Just X] O) = True
  Won (State '[a,b,Just X,c,Just X,d,Just X,e,f] O) = True
  Won (State '[Just O,Just O,Just O,a,b,c,d,e,f] X) = True
  Won (State '[a,b,c,Just O,Just O,Just O,d,e,f] X) = True
  Won (State '[a,b,c,d,e,f,Just O,Just O,Just O] X) = True
  Won (State '[Just O,a,b,Just O,c,d,Just O,e,f] X) = True
  Won (State '[a,Just O,b,c,Just O,d,e,Just O,f] X) = True
  Won (State '[a,b,Just O,c,d,Just O,e,f,Just O] X) = True
  Won (State '[Just O,a,b,c,Just O,d,e,f,Just O] X) = True
  Won (State '[a,b,Just O,c,Just O,d,Just O,e,f] X) = True
  Won (State '[a,b,c,d,e,f,g,h,i]                j) = False

data Simple :: [STATE] -> STATE -> * where
  Good :: Simple as (State bs x) ->
          Simple (State (Just x  ': bs) (Other x) ': MapCons Nothing as)
                 (State (Nothing ': bs) x)
  Skip :: Proxy y -> Simple as s -> Simple (MapCons (Just y) as) (Cons (Just y) s)
  Nil :: Simple '[] (State '[] x)

data Moves :: [STATE] -> STATE -> * where
  Lose :: Won s ~ True => Moves '[] s
  Play :: Won s ~ False => Simple as s -> Moves as s

-- IW (Free Moves) a (State [Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing] X)
