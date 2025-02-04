{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExplicitNamespaces #-}

-- | Update monad and update monad transformer.
-- 
-- Based on a blog post by Chris Penner:
-- 
-- "Update Monads: Variation on State Monads" https://chrispenner.ca/posts/update-monad
-- (Code included: https://github.com/chrispenner/update-monad)
--
-- The blog post also references a paper by Danel Ahman and Tarmo Uustalu as a source
--
-- "Update Monads: Cointerpreting Directed Containers" https://danelahman.github.io/papers/types13postproc.pdf
module Control.Monad.Trans.Update(
  type Update,
  UpdateT(.., Update),
  getState, putAction
) where

import Control.Monad ( ap )
import Control.Monad.Trans.Class ( MonadTrans(..) )

import Data.Semigroup.Action (Action(..))
import Data.Functor.Identity ( Identity(..) )

newtype UpdateT s x m a =
  UpdateT { runUpdateT :: x -> m (s, a) }
  deriving Functor

instance (Monoid s, Action s x, Monad m) => Applicative (UpdateT s x m) where
  pure a = UpdateT $ const (pure (mempty, a))
  (<*>) = ap

instance (Monoid s, Action s x, Monad m) => Monad (UpdateT s x m) where
  ma >>= k = UpdateT $ \x0 ->
    runUpdateT ma x0 >>= \(s0,a) ->
      runUpdateT (k a) (act s0 x0) >>= \(s1, b) ->
        pure (s1 <> s0, b)

instance (Monoid s, Action s x) => MonadTrans (UpdateT s x) where
  lift ma = UpdateT $ const ((,) mempty <$> ma)

getState :: (Monoid s, Monad m) => UpdateT s x m x
getState = UpdateT $ \x0 -> pure (mempty, x0)

putAction :: (Monad m) => s -> UpdateT s x m ()
putAction s1 = UpdateT $ const (pure (s1, ()))

type Update s x = UpdateT s x Identity

-- | Pattern synonym for non-transformer version
pattern Update :: (x -> (s, a)) -> Update s x a
pattern Update f <- UpdateT ((runIdentity .) -> f) where
  Update f = UpdateT (Identity . f)

{-# COMPLETE Update #-}