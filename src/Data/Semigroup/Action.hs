{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
module Data.Semigroup.Action where

import Data.Semigroup
import Data.Monoid qualified as Monoid
import Data.Group

import Data.Functor.Classes (Show1, Read1)
import AutoLift.Coercible (Reflected1(..))
import AutoLift.Functor qualified as ALF
import Data.Functor.Const
import Data.Bits
import Data.Void
import Data.Bifunctor (Bifunctor(..))
import Data.Monoid (Ap(..))

-- | Type equipped with left semigroup action.
-- 
-- 'act' must satisfy the following equation.
--
-- > s1 `act` (s2 `act` x) === (s1 <> s2) `act` x
--
-- Additionally, if `s` is @Monoid@, the following equation must be satisfied too.
--
-- > mempty `act` x = x
class (Semigroup s) => Action s x | x -> s where

  -- | Left semigroup action
  --
  -- To implement an instance of @Action@, you can omit the definition of @act@
  -- if @x@ is the same type to @s@.
  act :: s -> x -> x
  default act :: (s ~ x) => s -> x -> x
  act = (<>)

  -- | Left semigroup action repeated @n@ times.
  --
  -- For positive integer @n@, the following should satisfy.
  -- 
  -- > actNtimes n s x
  -- >  === act s $ act s $ ... n times ... $ x
  -- >  === act ('stimes' n s) x
  -- 
  -- As long as @s@ is @Monoid@, @actNtimes n@ must be defined for @n = 0@:
  --
  -- > actNtimes 0 s x === act 'mempty' x === x
  --
  -- As long as @s@ is @Group@, @actNtimes n@ for negative @n@ must be defined too:
  -- 
  -- > actNtimes n s x === actNtimes (negate n) ('invert' s) x === act ('pow' s n)
  -- 
  -- It is allowed to define @actNtimes n@ for @n = 0@ (
  -- negative value of @n@) even when @s@ is not @Monoid@ (@Group@),
  -- but there is no guarantee on the result.
  actNtimes :: Integral b => b -> s -> x -> x
  actNtimes n s = act (stimes n s)

infixr 6 `act`

actNtimesMonoid :: (Integral b, Action s x, Monoid s) => b -> s -> x -> x
actNtimesMonoid n s = act (mtimesDefault n s)

actNtimesGroup :: (Integral b, Action s x, Group s) => b -> s -> x -> x
actNtimesGroup n s = act (pow s n)

-- | Right semigroup actions.
class (Semigroup s) => RightAction s x | x -> s where

  -- | Rihgt semigroup action
  ract :: x -> s -> x
  default ract :: (s ~ x) => x -> s -> x
  ract = (<>)

  -- | Right semigroup action repeated @n@ times.
  ractNtimes :: Integral b => b -> x -> s -> x
  ractNtimes n x s = ract x (stimes n s)

infixl 7 `ract`

ractNtimesMonoid :: (Integral b, RightAction s x, Monoid s) => b -> x -> s -> x
ractNtimesMonoid n x s = ract x (mtimesDefault n s)

ractNtimesGroup :: (Integral b, RightAction s x, Group s) => b -> x -> s -> x
ractNtimesGroup n x s = ract x (pow s n)

-- trivial instances

instance Action () ()
instance RightAction () ()

instance Action Void Void
instance RightAction Void Void

-- | Trivial action
instance Semigroup s => Action s (Const a s) where
  act _ x = x

instance Semigroup s => RightAction s (Const a s) where
  ract = const

-- | Action mapped under a functor
newtype Mapped f x = Mapped { getMapped :: f x }
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

deriving via (ALF.Reflected1 (Mapped f))
  instance (Show1 f, Functor f) => Show1 (Mapped f)
deriving via (ALF.Reflected1 (Mapped f))
  instance (Read1 f, Functor f) => Read1 (Mapped f)

instance (Functor f, Action s x) => Action s (Mapped f x) where
  act s (Mapped fx) = Mapped (act s <$> fx)

instance (Functor f, RightAction s x) => RightAction s (Mapped f x) where
  ract (Mapped fx) s = Mapped ((`ract` s) <$> fx)

-- product instances

instance (Action s x, Action s' x') => Action (s,s') (x,x') where
  act ~(s,s') (x,x') = (act s x, act s' x')

instance (Action s x, Action s' x', Action s'' x'') => Action (s,s',s'') (x,x',x'') where
  act ~(s,s',s'') (x,x',x'') = (act s x, act s' x', act s'' x'')

-- sum instances

instance (Action s x, Action s x') => Action s (Either x x') where
  act s = bimap (act s) (act s)

instance (RightAction s x, RightAction s x') => RightAction s (Either x x') where
  ract xx s = bimap (`ract` s) (`ract` s) xx

-- Acting on contravariant position

-- | Function type @k -> v@ viewed as \"values of @v@ placed on locations indexed by @k@\".
-- 
-- Applying semigroup actions on places @k@ is also an action on @Placed k v@,
-- except it switches left action and right action.
newtype Placed k v = Placed { getPlaced :: k -> v }
   deriving (Functor, Applicative, Monad) via ((->) k)

instance Action s k => RightAction s (Placed k v) where
  ract (Placed f) s = Placed $ f . act s

  -- (Placed f) `ract` s1 `ract` s2
  -- = Placed (f . act s1) `ract` s2
  -- = Placed (f . act s1 . act s2)
  -- = Placed (\k -> f (act s1 (act s2 k)))
  -- = Placed (\k -> f (act (s1 <> s2) k))
  -- = Placed (f . act (s1 <> s2))
  -- = Placed f `ract` (s1 <> s2)

instance RightAction s k => Action s (Placed k v) where
  act s (Placed f) = Placed $ f . (`ract` s)

  -- s1 `act` s2 `act` Placed f
  -- = s1 `act` Placed (f . (`ract` s2))
  -- = Placed (f . (`ract` s2) . (`ract` s1))
  -- = Placed (\k -> f ((k `ract` s1) `ract` s2)
  -- = Placed (\k -> f (k `ract` (s1 <> s2)))
  -- = Placed (f . (`ract` (s1 <> s2)))
  -- = (s1 <> s2) `act` Placed f

-- "regular" instances

newtype Regular s = Regular { getRegular :: s }
    deriving stock (Show, Read, Eq, Ord)
    deriving (Show1, Read1) via (Reflected1 Regular)

instance (Semigroup s) => Action s (Regular s) where
  act s (Regular x) = Regular (s <> x)

instance (Semigroup s) => RightAction s (Regular s) where
  ract (Regular x) s = Regular (x <> s)

instance Action (Endo a) (Endo a)
instance Num a => Action (Sum a) (Sum a)
instance Num a => Action (Product a) (Product a)
instance Action Any Any
instance Action All All
instance Ord a => Action (Min a) (Min a)
instance Ord a => Action (Max a) (Max a)
instance Action (Last a) (Last a)
instance Action (First a) (First a)
instance Action (Monoid.Last a) (Monoid.Last a)
instance Action (Monoid.First a) (Monoid.First a)
instance Bits a => Action (And a) (And a)
instance Bits a => Action (Xor a) (Xor a)
instance Bits a => Action (Ior a) (Ior a)
instance FiniteBits a => Action (Iff a) (Iff a)

instance RightAction (Endo a) (Endo a)
instance Num a => RightAction (Sum a) (Sum a)
instance Num a => RightAction (Product a) (Product a)
instance RightAction Any Any
instance RightAction All All
instance Ord a => RightAction (Min a) (Min a)
instance Ord a => RightAction (Max a) (Max a)
instance RightAction (Last a) (Last a)
instance RightAction (First a) (First a)
instance RightAction (Monoid.Last a) (Monoid.Last a)
instance RightAction (Monoid.First a) (Monoid.First a)
instance Bits a => RightAction (And a) (And a)
instance Bits a => RightAction (Xor a) (Xor a)
instance Bits a => RightAction (Ior a) (Ior a)
instance FiniteBits a => RightAction (Iff a) (Iff a)

-- Dual actions

instance RightAction s x => Action (Dual s) (Dual x) where
  act (Dual s) (Dual x) = Dual $ x `ract` s

instance Action s x => RightAction (Dual s) (Dual x) where
  ract (Dual x) (Dual s) = Dual $ s `act` x

-- Applying endomorphism

newtype Pt a = Pt a
    deriving stock (Show, Read, Eq, Ord)
    deriving (Show1, Read1) via (Reflected1 Pt)

unPt :: Pt a -> a
unPt (Pt a) = a

instance Action (Endo a) (Pt a) where
  act (Endo f) (Pt a) = Pt (f a)

-- Lifting through applicative

instance (Applicative f, Action s x) => Action (Ap f s) (Ap f x) where
  act (Ap fs) (Ap fx) = Ap (liftA2 act fs fx)

instance (Applicative f, RightAction s x) => RightAction (Ap f s) (Ap f x) where
  ract (Ap fx) (Ap fs) = Ap (liftA2 ract fx fs)