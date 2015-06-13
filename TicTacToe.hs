{-# LANGUAGE PolyKinds, DataKinds, ConstraintKinds, TypeOperators, TypeFamilies #-}

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
  Won (State '[Just x,Just x,Just x,a,b,c,d,e,f] (Other x)) = True
  Won (State '[a,b,c,Just x,Just x,Just x,d,e,f] (Other x)) = True
  Won (State '[a,b,c,d,e,f,Just x,Just x,Just x] (Other x)) = True
  Won (State '[Just x,a,b,Just x,c,d,Just x,e,f] (Other x)) = True
  Won (State '[a,Just x,b,c,Just x,d,e,Just x,f] (Other x)) = True
  Won (State '[a,b,Just x,c,d,Just x,e,f,Just x] (Other x)) = True
  Won (State '[Just x,a,b,c,Just x,d,e,f,Just x] (Other x)) = True
  Won (State '[a,b,Just x,c,Just x,d,Just x,e,f] (Other x)) = True
  Won (State '[a,b,c,d,e,f,g,h,i]                x        ) = False

data Simple :: [STATE] -> STATE -> * where
  Good :: Simple as (State bs x) ->
          Simple (State (Just x  ': bs) (Other x) ': MapCons Nothing as)
                 (State (Nothing ': bs) x)
  Skip :: Simple as s -> Simple (MapCons (Just y) as) (Cons (Just y) s)
  Nil :: Simple '[] (State '[] x)

data Moves :: [STATE] -> STATE -> * where
  Lose :: Won s ~ True => Moves '[] s
  Play :: Won s ~ False => Simple as s -> Moves as s

-- IW (Free Moves) a (State [Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing] X)
