{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Control.Comonad.Act(
  Act(..), mapAct, locate, direct,

  toStore, fromStore,

  ActT(..),
  distributeAct
) where

import Control.Comonad (Comonad(..))
import Control.Comonad.Store (Store, store, pos, peek)

import Data.Semigroup.Action (Action(..), Torsor (..))
import Control.Comonad.Trans.Class (ComonadTrans(..))
import Control.Comonad.Hoist.Class (ComonadHoist(..))

data Act g x a = Act x (g -> a)
  deriving Functor

mapAct :: (g' -> g) -> (x -> x') -> Act g x a -> Act g' x' a
mapAct opg opx (Act x f) = Act (opx x) (f . opg)

instance (Semigroup g, Action g x) => Action g (Act g x a) where
  act g' (Act x0 f) = Act (act g' x0) (f . (<> g'))

instance (Monoid g, Action g x) => Comonad (Act g x) where
  extract (Act _ f) = f mempty
  duplicate w@(Act x0 _) = Act x0 $ \g' -> act g' w

locate :: Act g x a -> x
locate (Act x _) = x

direct :: g -> Act g x a -> a
direct g (Act _ f) = f g

-- | When the action is @'Torsor' g x@, there is a comonad isomorphism to @Store x@
toStore :: Torsor g x => Act g x a -> Store x a
toStore (Act x0 f) = store (\x1 -> f (x1 `difference` x0)) x0

-- | Comonad morphism from @Store x@. It is the inverse of 'toStore' if the action on @x@ is
-- @Torsor@.
fromStore :: Action g x => Store x a -> Act g x a
fromStore sa = Act x0 (\g' -> f (act g' x0))
  where
    x0 = pos sa
    f x1 = peek x1 sa

----

newtype ActT g x w a = ActT { runActT :: w (Act g x a) }
    deriving Functor

instance (Monoid g, Action g x, Comonad w) => Comonad (ActT g x w) where
  extract = extract . extract . runActT
  duplicate = fmap ActT . ActT . fmap distributeAct . duplicate . fmap duplicate . runActT

-- | Any comonad distributes over @Act@
distributeAct :: (Comonad w) => w (Act g x a) -> Act g x (w a)
distributeAct wa = Act (locate (extract wa)) (\g -> direct g <$> wa)

instance (Monoid g, Action g x) => ComonadTrans (ActT g x) where
  lower = fmap extract . runActT

instance ComonadHoist (ActT g x) where
  cohoist nat = ActT . nat . runActT
