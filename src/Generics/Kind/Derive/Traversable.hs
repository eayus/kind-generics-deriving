{-# language AllowAmbiguousTypes   #-}
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
module Generics.Kind.Derive.Traversable where

import           Data.Kind
import           GHC.TypeLits
import           Generics.Kind

traverseDefaultPos :: forall v f as bs g.
                      (GenericK f, GenericK f,
                       GTraversable (RepK f) v as bs,
                       Applicative g)
                   => (Interpret ('Var v) as -> g (Interpret ('Var v) bs))
                   -> f :@@: as -> g (f :@@: bs)
traverseDefaultPos f = fmap (toK @_ @f @bs) . gtraverse @_ @(RepK f) @v @as @bs f . fromK @_ @f @as

traverseDefault :: forall f a b g. (GenericK f, GenericK f,
                   GTraversable (RepK f) 'VZ (LoT1 a) (LoT1 b), Applicative g)
                => (a -> g b) -> f a -> g (f b)
traverseDefault = traverseDefaultPos @'VZ @f @(LoT1 a) @(LoT1 b)

class GTraversable (f :: LoT k -> Type) (v :: TyVar k Type)
                   (as :: LoT k) (bs :: LoT k) where
  gtraverse :: Applicative g
            => (Interpret ('Var v) as -> g (Interpret ('Var v) bs))
            -> f as -> g (f bs)

instance GTraversable U1 v as bs where
  gtraverse _ U1 = pure U1

instance forall f v as bs i c. GTraversable f v as bs
         => GTraversable (M1 i c f) v as bs where
  gtraverse v (M1 x) = M1 <$> gtraverse @_ @f @v @as @bs v x

instance forall f g v as bs. (GTraversable f v as bs, GTraversable g v as bs)
         => GTraversable (f :+: g) v as bs where
  gtraverse v (L1 x) = L1 <$> gtraverse @_ @f @v @as @bs v x
  gtraverse v (R1 x) = R1 <$> gtraverse @_ @g @v @as @bs v x

instance forall f g v as bs. (GTraversable f v as bs, GTraversable g v as bs)
         => GTraversable (f :*: g) v as bs where
  gtraverse v (x :*: y) = (:*:) <$> gtraverse @_ @f @v @as @bs v x
                                <*> gtraverse @_ @g @v @as @bs v y

instance forall c f v as bs z.
         (Interpret c as => GTraversable f v as bs, z ~ Interpret c bs, Interpret c as => z)
         => GTraversable (c :=>: f) v as bs where
  gtraverse v (SuchThat x) = SuchThat <$> gtraverse @_ @f @v @as @bs v x

instance forall k f v as bs.
         (forall (t :: k). GTraversable f ('VS v) (t ':&&: as) (t ':&&: bs))
         => GTraversable (Exists k f) v as bs where
  gtraverse v (Exists (x :: f (t ':&&: x)))
    = Exists <$> gtraverse @_ @f @('VS v) @(t ':&&: x) @(t ':&&: _) v x

instance forall t v as bs. GTraversableArg t v as bs (ContainsTyVar v t)
         => GTraversable (Field t) v as bs where
  gtraverse v (Field x) = Field <$> gtraversef @_ @t @v @as @bs @(ContainsTyVar v t) v x

class GTraversableArg (t :: Atom d Type) (v :: TyVar d Type)
                      (as :: LoT d) (bs :: LoT d) (p :: Bool) where
  gtraversef :: Applicative g
             => (Interpret ('Var v) as -> g (Interpret ('Var v) bs))
             -> Interpret t as -> g (Interpret t bs)

instance (Interpret t as ~ Interpret t bs) => GTraversableArg t v as bs 'False where
  gtraversef _ = pure

instance ( Traversable (Interpret f as), Interpret f as ~ Interpret f bs
         , GTraversableArg x v as bs (ContainsTyVar v x))
         => GTraversableArg (f ':@: x) v as bs 'True where
  gtraversef f x = traverse (gtraversef @_ @x @v @as @bs @(ContainsTyVar v x) f) x

-- -- We found the same variable
-- instance GTraversableArg ('Var 'VZ) 'VZ (a ':&&: as) (b ':&&: bs) 'True where
--   gtraversef f x = f x
-- -- We need to keep looking
-- instance forall d (v :: TyVar d Type) n r as s bs isthere.
--          GTraversableArg ('Var v) n as bs isthere
--          => GTraversableArg ('Var ('VS v)) ('VS n) (r ':&&: as) (s ':&&: bs) isthere where
--   gtraversef f x = gtraversef @d @('Var v) @n @as @bs @isthere f x
-- -- If we arrive to another we do not want, keep it as it is
-- instance TypeError ('Text "Should never get here")
--          => GTraversableArg ('Var 'VZ) ('VS n) (r ':&&: as) (r ':&&: bs) 'True where
--   gtraversef _ = pure

instance (w ~ v) => GTraversableArg ('Var w) v as bs 'True where
    gtraversef f x = f x

