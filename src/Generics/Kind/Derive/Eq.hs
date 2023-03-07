{-# language AllowAmbiguousTypes   #-}
{-# language ConstraintKinds       #-}
{-# language DataKinds             #-}
{-# language FlexibleContexts      #-}
{-# language FlexibleInstances     #-}
{-# language MultiParamTypeClasses #-}
{-# language PolyKinds             #-}
{-# language QuantifiedConstraints #-}
{-# language ScopedTypeVariables   #-}
{-# language TypeApplications      #-}
{-# language TypeFamilies          #-}
{-# language TypeOperators         #-}
{-# language UndecidableInstances  #-}
module Generics.Kind.Derive.Eq where

import           Data.Kind
import           GHC.TypeLits
import           Generics.Kind

geq' :: forall t. (GenericK t, GEq (RepK t), ReqsEq (RepK t) 'LoT0)
     => t -> t -> Bool
geq' x y = geq (fromK @_ @t @'LoT0 x) (fromK @_ @t @'LoT0 y)

class GEq (f :: LoT k -> Type) where
  type family ReqsEq f (tys :: LoT k) :: Constraint
  geq :: ReqsEq f tys => f tys -> f tys -> Bool

instance GEq U1 where
  type ReqsEq U1 tys = ()
  geq U1 U1 = True

instance GEq f => GEq (M1 i c f) where
  type ReqsEq (M1 i c f) tys = ReqsEq f tys
  geq (M1 x) (M1 y) = geq x y

instance (GEq f, GEq g) => GEq (f :+: g) where
  type ReqsEq (f :+: g) tys = (ReqsEq f tys, ReqsEq g tys)
  geq (L1 x) (L1 y) = geq x y
  geq (R1 x) (R1 y) = geq x y
  geq _      _      = False

instance (GEq f, GEq g) => GEq (f :*: g) where
  type ReqsEq (f :*: g) tys = (ReqsEq f tys, ReqsEq g tys)
  geq (x1 :*: x2) (y1 :*: y2) = geq x1 y1 && geq x2 y2

instance GEq (Field t) where
  type ReqsEq (Field t) tys = Eq (Interpret t tys)
  geq (Field x) (Field y) = x == y

instance GEq f => GEq (c :=>: f) where
  type ReqsEq (c :=>: f) tys = ReqsEq f tys
  -- really we want          = Interpret c tys => GEq f tys
  geq (SuchThat x) (SuchThat y) = geq x y

instance TypeError ('Text "Existentials are not supported")
         => GEq (Exists k f) where
  type ReqsEq (Exists k f) tys = TypeError ('Text "Existentials are not supported")
  geq = undefined
