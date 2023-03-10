{-# language AllowAmbiguousTypes   #-}
{-# language DataKinds             #-}
{-# language FlexibleContexts      #-}
{-# language FlexibleInstances     #-}
{-# language GADTs                 #-}
{-# language MultiParamTypeClasses #-}
{-# language PolyKinds             #-}
{-# language QuantifiedConstraints #-}
{-# language RankNTypes            #-}
{-# language ScopedTypeVariables   #-}
{-# language TypeApplications      #-}
{-# language TypeFamilies          #-}
{-# language TypeOperators         #-}
{-# language UndecidableInstances  #-}
module Generics.Kind.Derive.KFunctor where

import           Data.Kind
import           Data.PolyKinded.Functor
import           Data.Proxy

import           Generics.Kind

kfmapDefault :: forall k (f :: k) v as bs. (GenericK f, GenericK f, GFunctor (RepK f) v as bs)
             => Mappings v as bs -> f :@@: as -> f :@@: bs
kfmapDefault v = toK @k @f @bs . gfmap v . fromK @k @f @as

fmapDefault' :: forall (f :: Type -> Type) a b.
                (GenericK f, GenericK f,
                 GFunctor (RepK f) '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0))
              => (a -> b) -> f a -> f b
fmapDefault' f = kfmapDefault (f :^: M0 :: Mappings '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0))

class GFunctor (f :: LoT k -> Type) (v :: Variances) (as :: LoT k) (bs :: LoT k) where
  gfmap :: Mappings v as bs -> f as -> f bs

instance GFunctor U1 v as bs where
  gfmap _ U1 = U1

instance GFunctor f v as bs => GFunctor (M1 i c f) v as bs where
  gfmap v (M1 x) = M1 (gfmap v x)

instance (GFunctor f v as bs, GFunctor g v as bs)
         => GFunctor (f :+: g) v as bs where
  gfmap v (L1 x) = L1 (gfmap v x)
  gfmap v (R1 x) = R1 (gfmap v x)

instance (GFunctor f v as bs, GFunctor g v as bs)
         => GFunctor (f :*: g) v as bs where
  gfmap v (x :*: y) = gfmap v x :*: gfmap v y

instance (Interpret c as => GFunctor f v as bs, {- Ty c as => -} Interpret c bs)
         => GFunctor (c :=>: f) v as bs where
  gfmap v (SuchThat x) = SuchThat (gfmap v x)

instance forall f v as bs.
         (forall (t :: Type). GFunctor f ('Co ': v) (t ':&&: as) (t ':&&: bs))
         => GFunctor (Exists Type f) v as bs where
  gfmap v (Exists (x :: f (t ':&&: x)))
    = Exists (gfmap ((id :^: v) :: Mappings ('Co ': v) (t ':&&: as) (t ':&&: bs)) x)

class GFunctorArg (t :: Atom d Type)
                  (v :: Variances) (intended :: Variance)
                  (as :: LoT d) (bs :: LoT d) where
  gfmapf :: Proxy t -> Proxy intended
         -> Mappings v as bs
         -> Mapping intended (Interpret t as) (Interpret t bs)

instance forall t v as bs. GFunctorArg t v 'Co as bs
         => GFunctor (Field t) v as bs where
  gfmap v (Field x) = Field (gfmapf (Proxy @t) (Proxy @'Co) v x)

instance GFunctorArg ('Kon t) v 'Co as bs where
  gfmapf _ _ _ = id
instance GFunctorArg ('Kon t) v 'Contra as bs where
  gfmapf _ _ _ = id

instance forall d (f :: Atom (Type -> d) Type) v (as :: LoT d) (bs :: LoT d).
         (forall (t :: Type). GFunctorArg f ('Co ': v) 'Co (t ':&&: as) (t ':&&: bs))
         => GFunctorArg ('ForAll f) v 'Co as bs where
  gfmapf _ _ v x = fromWrappedI $ go $ toWrappedI x
    where
      go :: forall (t :: Type). WrappedI f (t ':&&: as) -> WrappedI f (t ':&&: bs)
      go (WrapI p) = WrapI (gfmapf @(Type -> d) @f @('Co ': v) @'Co @(t ':&&: as) @(t ':&&: bs)
                           Proxy Proxy (id :^: v) p)

instance GFunctorArg ('Var 'VZ) (r ': v) r (a ':&&: as) (b ':&&: bs) where
  gfmapf _ _ (f :^: _) = f

instance forall vr pre v intended a as b bs.
         GFunctorArg ('Var vr) v intended as bs
         => GFunctorArg ('Var ('VS vr)) (pre ': v) intended (a ':&&: as) (b ':&&: bs) where
  gfmapf _ _ (_ :^: rest) = gfmapf (Proxy @('Var vr)) (Proxy @intended) rest

instance forall f x v v1 as bs.
         (KFunctor f '[v1] (Interpret x as ':&&: 'LoT0) (Interpret x bs ':&&: 'LoT0),
          GFunctorArg x v v1 as bs)
         => GFunctorArg (f :$: x) v 'Co as bs where
  gfmapf _ _ v = kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^: M0)

instance forall f x y v v1 v2 as bs.
         (KFunctor f '[v1, v2] (Interpret x as ':&&: Interpret y as ':&&: 'LoT0)
                               (Interpret x bs ':&&: Interpret y bs ':&&: 'LoT0),
          GFunctorArg x v v1 as bs, GFunctorArg y v v2 as bs)
         => GFunctorArg (f :$: x ':@: y) v 'Co as bs where
  gfmapf _ _ v = kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^:
                        gfmapf (Proxy @y) (Proxy @v2) v :^: M0)

instance forall f x y z v v1 v2 v3 as bs.
         (KFunctor f '[v1, v2, v3] (Interpret x as ':&&: Interpret y as ':&&: Interpret z as ':&&: 'LoT0)
                                   (Interpret x bs ':&&: Interpret y bs ':&&: Interpret z bs ':&&: 'LoT0),
          GFunctorArg x v v1 as bs, GFunctorArg y v v2 as bs, GFunctorArg z v v3 as bs)
         => GFunctorArg (f :$: x ':@: y ':@: z) v 'Co as bs where
  gfmapf _ _ v = kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^:
                        gfmapf (Proxy @y) (Proxy @v2) v :^:
                        gfmapf (Proxy @z) (Proxy @v3) v :^: M0)
