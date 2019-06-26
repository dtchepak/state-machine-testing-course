{-# OPTIONS_GHC -Wno-unused-binds -Wno-unused-imports #-}
{-# LANGUAGE RankNTypes #-}
module LawPropertiesBonus 
  ( firstPrismLaw
  , secondPrismLaw
  , thirdPrismLaw
  , _Empty
  , _Node
  ) where

import           Control.Lens   (Prism', matching, preview, prism, prism', review)

import           Hedgehog
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range

import           MyBTree        (MyBTree (..), foldTree)

-- Complete the following prisms, then write properties that check the Prism laws hold.
-- Prism' s a = Prism s s a a
-- prism' :: (b -> s) -> (s -> Maybe a) -> Prism s s a b
-- prism' :: (a -> s) -> (s -> Maybe a) -> Prism s s a a
-- prism' :: (() -> MyBTree k a) -> (MyBTree k a -> Maybe ()) -> Prism' (MyBTree k a) ()
_Empty :: Prism' (MyBTree k a) ()
_Empty =
    let getEmpty Empty = Just ()
        getEmpty _     = Nothing
    in prism' (const Empty) getEmpty

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

_Node :: Prism' (MyBTree k a) (MyBTree k a, (k, a), MyBTree k a)
_Node =
    let getNode Empty = Nothing
        getNode (Node l n r) = Just (l, n, r)
    in prism' (uncurry3 Node) getNode

-- First, if I re or review a value with a Prism and then preview or use (^?),
-- I will get it back:
--
-- preview l (review l b) ≡ Just b
--
firstPrismLaw :: (Eq b, Show b) => Gen b -> Prism' a b -> Property
firstPrismLaw _gen _p = property $ do
    b <- forAll _gen
    preview _p (review _p b) === Just b

-- Second, if you can extract a value a using a Prism l from a value s, then
-- the value s is completely described by l and a:
--
-- preview l s ≡ Just a ==> review l a ≡ s
secondPrismLaw :: (Eq s, Show s) => Gen s -> Prism' s a -> Property
secondPrismLaw _gen _p = property $ do
    s <- forAll _gen
    maybe success (\a -> review _p a === s) (preview _p s)

-- Third, if you get non-match t, you can convert it result back to s:
--
-- matching l s ≡ Left t ==> matching l t ≡ Left s
thirdPrismLaw :: (Eq a, Show a, Eq s, Show s) => Gen s -> Prism' s a -> Property
thirdPrismLaw _gen _p = property $ do
    s <- forAll _gen
    either (\t -> matching _p t === Left s) (const success) (matching _p s)
