
{-# LANGUAGE TypeOperators #-}
module Check where

import Prelude hiding (zip)
import Data.These
import Data.Zip
import Data.Bifunctor

import Data.Bifunctor.Assoc (Assoc (..))
import Data.Bifunctor.Swap  (Swap (..))

type (◇) = These

(∩) :: (Zip f) => f a -> f b -> f (a, b)
(∩) = zip
infix 6 ∩

(∪) :: (Semialign f) => f a -> f b -> f (a ◇ b)
(∪) = align
infix 6 ∪

foo :: (a, b ◇ c) ◇ (c, b ◇ c) -> (a, b) ◇ c
foo = bar . bimap str fst

str :: (a, b ◇ c) -> (a, b) ◇ c
str (a, This b) = This (a,b)
str (_, That c) = That c
str (a, These b c) = These (a, b) c

bar :: ((a, b) ◇ c) ◇ c -> (a, b) ◇ c
bar = second rightBias . assoc

leftBias, rightBias :: c ◇ c -> c
leftBias (This c) = c
leftBias (That c') = c'
leftBias (These c _) = c

rightBias (This c) = c
rightBias (That c') = c'
rightBias (These _ c') = c'

toThis :: a ◇ b -> a ◇ b
toThis (This a)    = This a
toThis (These a _) = This a
toThis (That b)    = That b

-----------------------
-- Equation type checks
-----------------------

data Eqn a = Eqn

(≡), (--->) :: a -> Eqn a -> Eqn a
(≡) = const id
(--->) = const id
infixr 0 ≡
infixr 0 --->

($.) :: (a -> b) -> a -> b
($.) = id

infixl 1 $.

undistrPTProp :: (a ◇ b, c) -> Eqn (a ◇ b, c)
undistrPTProp (This a, c) =
    undistrPairThese . distrPairThese $. (This a, c)
 ≡ undistrPairThese (This (a, c))
 ≡ (This a, c)
 ---> Eqn
undistrPTProp (That b, c) =
    undistrPairThese . distrPairThese $. (That b, c)
 ≡ (That b, c)
 ≡ undistrPairThese $. That (b, c)
 ---> Eqn
undistrPTProp (These a b, c) =
    undistrPairThese . distrPairThese $. (These a b, c)
 ≡ undistrPairThese $. These (a, c) (b, c)
 ≡ (These a b, c)
 ---> Eqn

fooProp :: (a ◇ c, b ◇ c) -> Eqn ((a, b) ◇ c) 
fooProp (ac, bc) = case ac of
  This a ->
       foo (distrPairThese (This a, bc))
    ≡ foo (This (a, bc))
    ≡ bar . bimap str fst $. This (a, bc)
    ≡ bar $. This (str (a,bc))
    ---> case bc of
      This b -> 
            bar $. This (str (a, This b))
        ≡ second rightBias . assoc $. This (This (a,b))
        ≡ This (a,b)
        ≡ undistrThesePair (This a, This b)
        ---> Eqn
      That c ->
          bar $. This (str (a, That c))
        ≡ second rightBias . assoc $. This (That c)
        ≡ second rightBias $. That (This c)
        ≡ That c
        ≡ undistrThesePair (This a, That c)
        ---> Eqn
      These b c ->
          bar $. This (str (a, These b c))
        ≡ second rightBias . assoc $. This (These (a,b) c)
        ≡ second rightBias $. These (a,b) (This c)
        ≡ These (a,b) c
        ≡ undistrThesePair (This a, These b c)
        ---> Eqn
  That c ->
       foo (distrPairThese (That c, bc))
    ≡ foo (That (c, bc))
    ≡ bar . bimap str fst $. That (c, bc)
    ≡ bar $. That c
    ≡ second rightBias . assoc $. That c
    ≡ That c
    ≡ undistrThesePair (That c, bc)
    ---> Eqn
  These a c ->
       foo (distrPairThese (These a c, bc))
    ≡ bar . bimap str fst $. These (a, bc) (c, bc)
    ≡ bar $. These (str (a,bc)) c
    ---> case bc of
      This b ->
           bar $. These (str (a, This b)) c
        ≡ second rightBias . assoc $. These (This (a,b)) c
        ≡ second rightBias $. These (a,b) (That c)
        ≡ These (a,b) c
        ≡ undistrThesePair (These a c, This b)
        ---> Eqn
      That c' ->
           bar $. These (str (a, That c')) c
        ≡ second rightBias . assoc $. These (That c') c
        ≡ second rightBias $. That (These c' c)
        ≡ That c
        ≡ undistrThesePair (These a c, That c')
        ---> Eqn
      These b c' ->
           bar $. These (str (a, These b c')) c
        ≡ second rightBias . assoc $. These (These (a,b) c') c
        ≡ second rightBias $. These (a,b) (These c' c)
        ≡ These (a,b) c
        ≡ undistrThesePair (These a c, These b c')
        ---> Eqn

-- str ≡ bimap swap fst . distrPairThese . swap
strProp :: (a, b ◇ c) -> Eqn ((a, b) ◇ c)
strProp (a, This b) = 
     bimap swap fst . distrPairThese . swap $. (a, This b)
  ≡ bimap swap fst . distrPairThese $. (This b, a)
  ≡ bimap swap fst $. This (b,a)
  ≡ This (a,b)
  ≡ str (a, This b)
  ---> Eqn
strProp (a, That c) =
     bimap swap fst . distrPairThese . swap $. (a, That c)
  ≡ bimap swap fst . distrPairThese $. (That c, a)
  ≡ bimap swap fst $. That (c,a)
  ≡ That c
  ≡ str (a, That c)
  ---> Eqn
strProp (a, These b c) =
     bimap swap fst . distrPairThese . swap $. (a, These b c)
  ≡ bimap swap fst . distrPairThese $. (These b c, a)
  ≡ bimap swap fst $. These (b,a) (c,a)
  ≡ These (a,b) c
  ≡ str (a, These b c)
  ---> Eqn

mainProp :: (Zip f) => f a -> f b -> f c -> Eqn (f ((a,b) ◇ c))
mainProp xs ys zs =
  -- The RHS of Distr(1)
    undistrThesePair <$> (xs ∪ zs) ∩ (ys ∪ zs)
  -- Rewrite using foo
  ≡ foo . distrPairThese <$> (xs ∪ zs) ∩ (ys ∪ zs)
  -- Apply Distr(2)
  ≡ foo <$> (xs ∩ (ys ∪ zs)) ∪ (zs ∩ (ys ∪ zs))
  ≡ bar . bimap str fst <$> (xs ∩ (ys ∪ zs)) ∪ (zs ∩ (ys ∪ zs))
  -- Free theorem of align
  ≡ bar <$> (str <$> xs ∩ (ys ∪ zs)) ∪ (fst <$> zs ∩ (ys ∪ zs))
  -- Absorption + commutativity of align
  ≡ bar <$> (str <$> xs ∩ (ys ∪ zs)) ∪ zs
  -- Lemma(1)
  ≡ bar <$> (bimap swap fst . distrPairThese . swap <$> xs ∩ (ys ∪ zs)) ∪ zs
  -- Commutativity of zip
  ≡ bar <$> (bimap swap fst . distrPairThese <$> (ys ∪ zs) ∩ xs) ∪ zs
  -- Apply Distr(2)
  ≡ bar <$> (bimap swap fst <$> (ys ∩ xs) ∪ (zs ∩ xs)) ∪ zs
  -- Free theorem of zip
  ≡ bar <$> ((swap <$> ys ∩ xs) ∪ (fst <$> zs ∩ xs)) ∪ zs
  -- Commutativity of zip
  ≡ bar <$> ((xs ∩ ys) ∪ (fst <$> zs ∩ xs)) ∪ zs
  ≡ second rightBias . assoc <$> ((xs ∩ ys) ∪ (fst <$> zs ∩ xs)) ∪ zs
  -- Associativity of align
  ≡ second rightBias <$> (xs ∩ ys) ∪ ((fst <$> zs ∩ xs) ∪ zs)
  -- Free theorem of align
  ≡ (xs ∩ ys) ∪ (rightBias <$> (fst <$> zs ∩ xs) ∪ zs)
  -- Commutativity
  ≡ (xs ∩ ys) ∪ (rightBias . swap <$> zs ∪ (fst <$> zs ∩ xs))
  -- Lemma(2)
  ≡ (xs ∩ ys) ∪ (leftBias <$> zs ∪ (fst <$> zs ∩ xs))
  -- Free theorem of align
  ≡ (xs ∩ ys) ∪ (leftBias . second fst <$> zs ∪ (zs ∩ xs))
  -- Lemma(3)
  ≡ (xs ∩ ys) ∪ (leftBias . second fst . toThis <$> zs ∪ (zs ∩ xs))
  -- Absorption law
  ≡ (xs ∩ ys) ∪ (leftBias . second fst . This <$> zs)
  ≡ (xs ∩ ys) ∪ (leftBias . This <$> zs)
  ≡ (xs ∩ ys) ∪ zs
  -- The LHS of Distr(1)
  ---> Eqn
