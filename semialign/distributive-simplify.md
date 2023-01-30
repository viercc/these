# Distributivity law can be simplified

The documentation of [Zip](https://hackage.haskell.org/package/semialign-1.2/docs/Data-Zip.html#t:Zip) says an instance of `Zip` must satisfy the following Distributivity laws.

```haskell
-- The distributivity laws of Zip f
 
-- Each equation must hold for any
--   a, b, c :: Type
--   xs :: f a
--   ys :: f b
--   zs :: f c

                   align (zip xs ys) zs ≡ undistrThesePair <$> zip (align xs zs) (align ys zs)
distrPairThese <$> zip (align xs ys) zs ≡                      align (zip xs zs) (zip ys zs)
                   zip (align xs ys) zs ≡ undistrPairThese <$> align (zip xs zs) (zip ys zs)
```

Each of the three equations must hold. Let me name each equation as `Distr(1)` - `Distr(3)`.

```haskell
-- Distr(1)
align (zip xs ys) zs ≡ undistrThesePair <$> zip (align xs zs) (align ys zs)

-- Distr(2)
distrPairThese <$> zip (align xs ys) zs ≡ align (zip xs zs) (zip ys zs)

-- Distr(3)
zip (align xs ys) zs ≡ undistrPairThese <$> align (zip xs zs) (zip ys zs)
```

In this gist, I'll show that `Distr(2)` implies `Distr(1)` and `Distr(3)`. In other words,
`Distr(1)` and `Distr(3)` are redundant.

## Preparation of notation

For the cosmetic purpose, I'll use the following type synonyms and operators.

```haskell
{-# LANGUAGE TypeOperators #-}
type (◇) = These

(∩) :: (Zip f) => f a -> f b -> f (a, b)
(∩) = zip
infix 6 ∩

(∪) :: (Semialign f) => f a -> f b -> f (a ◇ b)
(∪) = align
infix 6 ∪
```

The choice of operators come from intuition that `zip` takes the intersection of "sets of places where values exist"
and `align` takes the union. Of course, "the set of places where values exist" is not a defined concept at all,
and this is just for memorizing what these operations do.

Using these notations, three equations are

```haskell
-- Distr(1)
(xs ∩ ys) ∪ zs ≡ undistrThesePair <$> (xs ∪ zs) ∩ (ys ∪ zs)

-- Distr(2)
distrPairThese <$> (xs ∪ ys) ∩ zs ≡ (xs ∩ zs) ∪ (ys ∩ zs)

-- Distr(3)
(xs ∪ ys) ∩ zs ≡ undistrPairThese <$> (xs ∩ zs) ∪ (ys ∩ zs)
```

## `Distr(2)` ⇒ `Distr(3)`

This implication holds, because `undistrPairThese . distrPairThese = id` holds.

```haskell
(xs ∪ ys) ∩ zs
    -- By undistrPairThese . distrPairThese = id
 ≡ undistrPairThese . distrPairThese <$> (xs ∪ ys) ∩ zs
    -- By Distr(2)
 ≡ undistrPairThese <$> (xs ∩ zs) ∪ (ys ∩ zs)
```

And `undistrPairThese . distrPairThese = id` can be confirmed by exhausting the possible cases.

```haskell
undistrPairThese . distrPairThese $ (This a, c)
 = undistrPairThese $ This (a, c)
 = (This a, c)

undistrPairThese . distrPairThese $ (That b, c)
 = undistrPairThese $ That (b, c)
 = (That b, c)

undistrPairThese . distrPairThese $ (These a b, c)
 = undistrPairThese $ These (a, c) (b, c)
 = (These a b, c)
```

For reference, the following is the definition of two functions.

```haskell
distrPairThese :: (a ◇ b, c) -> (a, c) ◇ (b, c)
distrPairThese (This a,    c) = This (a, c)
distrPairThese (That b,    c) = That (b, c)
distrPairThese (These a b, c) = These (a, c) (b, c)

undistrPairThese :: (a, c) ◇ (b, c) -> (a ◇ b, c)
undistrPairThese (This (a, c))         = (This a, c)
undistrPairThese (That (b, c))         = (That b, c)
undistrPairThese (These (a, c) (b, _)) = (These a b, c)
```

Note that these functions are not inverse each other, because `distrPairThese . undistrPairThese ≠ id`.

## `Distr(2)` ⇒ `Distr(1)`

Unlike `Distr(3)`, the proof of this implication is lengthy.
Firstly, why this seems to be possible: distributivity property of a lattice have similar a property.

> ***Distributivity of a lattice***
> 
> Let `A` be a lattice by the join (∨) and the meet (∧) operations. These two properties about `A` are equivalent each other.
> 
>  1. For all `x,y,z ∈ A`, `(x ∧ y) ∨ z = (x ∨ z) ∧ (y ∨ z)`
>  2. For all `x,y,z ∈ A`, `(x ∨ y) ∧ z = (x ∧ z) ∨ (y ∧ z)`
> 
> *Proof:* By duality, it is sufficient to prove either one implies the other one. Prove (2) ⇒ (1).
> (1) is true assuming (2) by the following calculation.
> 
> ```haskell
> -- The RHS of (1)
> (x ∨ z) ∧ (y ∨ z)
>   -- Apply (2) by substituting forall-ed variables (x => x, y => z, z => y ∨ z)
> = (x ∧ (y ∨ z)) ∨ (z ∧ (y ∨ z))
>   -- Use commutativity of ∨ and absorption
> = (x ∧ (y ∨ z)) ∨ z
>   -- Use commutativity of ∧
> = ((y ∨ z) ∧ x) ∨ z
>   -- Apply (2) by substituting forall-ed variables (x => y, y => z, z => x)
> = ((y ∧ x) ∨ (z ∧ x)) ∨ z
>   -- Use associativity of ∨
> = (y ∧ x) ∨ ((z ∧ x) ∨ z)
>   -- Use commutativity of ∧ and ∨
> = (x ∧ y) ∨ (z ∨ (z ∧ x))
>   -- Use absorption
> = (x ∧ y) ∨ z
>   -- The LHS of (1)
> ```

When the value of elements in `xs, ys, zs` are ignored, `Distr(1)` corresponds to distributive property (1) of a lattice,
and `Distr(2)` corresponds to property (2). I prove the implication `Distr(2) ⇒ Distr(1)` by carefully tracking the elements, while following the course of this proof about a lattice.

### Preparing auxiliary definitions

To mimick the above proof about a lattice, look for a way to rewrite the RHS of `Distr(1)`
to another equivalent form which is applicable the `Distr(2)` property.

More concretely, find `foo` function which fills the equation below.

```haskell
-- The RHS of Distr(1)
undistrThesePair <$> (xs ∪ zs) ∩ (ys ∪ zs)
 ≡ foo . distrPairThese <$> (xs ∪ zs) ∩ (ys ∪ zs)
--        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
--  Distr(2) can be applied here
```

And there is `foo` such that `foo . distrPairThese = undistrThesePair` holds.
By making some arbitrary choices among functions satisfying that equation,
`foo` can be defined as follows:

```haskell
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
```

Let me confirm this `foo` actually satisfy `foo . distrPairThese = undistrThesePair`.

```haskell
-- The goal is to show for all `acbc` below...
acbc :: (a ◇ c, b ◇ c)

-- This equation holds.
foo (distrPairThese acbc) = undistrThesePair acbc
```

The proof of the equation is done simply by exhausting every case.

```haskell
-- Case analysis on acbc
-- Case 1: acbc = (This a, bc)
foo (distrPairThese (This a, bc))
 = foo (This (a, bc))
 = bar . bimap str fst $ This (a, bc)
 = bar $ This (str (a,bc))
   -- Case analysis on bc
   -- Case 1-1: bc = This b
   bar $ This (str (a, This b))
    = second rightBias . assoc $ This (This (a,b))
    = This (a,b)
    = undistrThesePair (This a, This b)
   -- Case 1-2: bc = That c
   bar $ This (str (a, That c))
    = second rightBias . assoc $ This (That c)
    = second rightBias $ That (This c)
    = That c
    = undistrThesePair (This a, That c)
   -- Case 1-3: bc = These b c
   bar $ This (str (a, These b c))
    = second rightBias . assoc $ This (These (a,b) c)
    = second rightBias $ These (a,b) (This c)
    = These (a,b) c
    = undistrThesePair (This a, These b c)
-- Case 2: acbc = (That c, bc)
foo (distrPairThese (That c, bc))
 = foo (That (c, bc))
 = bar . bimap str fst $ That (c, bc)
 = bar $ That c
 = second rightBias . assoc $ That c
 = That c
 = undistrThesePair (That c, bc)
-- Case 3: acbc = (These a c, bc)
foo (distrPairThese (These a c, bc))
 = foo (These (a, bc) (c, bc))
 = bar . bimap str fst $ These (a, bc) (c, bc)
 = bar $ These (str (a,bc)) c
   -- Case analysis on bc
   -- Case 3-1: bc = This b
   bar $ These (str (a, This b)) c
    = second rightBias . assoc $ These (This (a,b)) c
    = second rightBias $ These (a,b) (That c)
    = These (a,b) c
    = undistrThesePair (These a c, This b)
   -- Case 3-2: bc = That c'
   bar $ These (str (a, That c')) c
    = second rightBias . assoc $ These (That c') c
    = second rightBias $ That (These c' c)
    = That c
    = undistrThesePair (These a c, That c')
   -- Case 3-3: bc = These b c'
   bar $ These (str (a, These b c')) c
    = second rightBias . assoc $ These (These (a,b) c') c
    = second rightBias $ These (a,b) (These c' c)
    = These (a,b) c
    = undistrThesePair (These a c, These b c')
```

### Lemmas

* *Lemma(1)*: `str` can alternatively written as follows.

  ```haskell
  str :: (a, b ◇ c) -> (a, b) ◇ c
  str = bimap swap fst . distrPairThese . swap
  ```

  * Proof.
  
    ```haskell
    bimap swap fst . distrPairThese . swap $ (a, This b)
     = bimap swap fst . distrPairThese $ (This b, a)
     = bimap swap fst $ This (b,a)
     = This (a,b)
     = str (a, This b)
    bimap swap fst . distrPairThese . swap $ (a, That c)
     = bimap swap fst . distrPairThese $ (That c, a)
     = bimap swap fst $ That (c,a)
     = That c
     = str (a, That c)
    bimap swap fst . distrPairThese . swap $ (a, These b c)
     = bimap swap fst . distrPairThese $ (These b c, a)
     = bimap swap fst $ These (b,a) (c,a)
     = These (a,b) c
     = str (a, These b c)
    ```

* *Lemma(2)*: `rightBias . swap = leftBias`.

   Proof is simple calculation.

* *Lemma(3)*: The following equation hold.

  ```haskell
  leftBias . second fst . toThis = leftBias . second fst
  ```

  Where `toThis` is a function that is not exported from the library,
  but used in the `Absorption` law of `Zip`.

  ```haskell
  -- Absorption law (but written using operators for this gist)
  fst <$> xs ∩ (xs ∪ ys) ≡ xs
  toThis <$> xs ∪ (xs ∩ ys) ≡ This <$> xs
    where
      toThis :: a ◇ b -> a ◇ b
      toThis (This a)    = This a
      toThis (These a _) = This a
      toThis (That b)    = That b
  ```

  * Proof.

    ```haskell
    leftBias . second fst . toThis $ This a
    = leftBias . second fst $ This a
    leftBias . second fst . toThis $ That ab
    = leftBias . second fst $ That ab

    leftBias . second fst . toThis $ These a ab
    = leftBias . second fst $ This a
    = a
    leftBias . second fst $ These a ab
    = leftBias $ These a (fst ab)
    = a
    ```

### The proof

```haskell
-- The RHS of Distr(1)
undistrThesePair <$> (xs ∪ zs) ∩ (ys ∪ zs)
-- Rewrite using foo
= foo . distrPairThese <$> (xs ∪ zs) ∩ (ys ∪ zs)
-- Apply Distr(2)
= foo <$> (xs ∩ (ys ∪ zs)) ∪ (zs ∩ (ys ∪ zs))
= bar . bimap str fst <$> (xs ∩ (ys ∪ zs)) ∪ (zs ∩ (ys ∪ zs))
-- Free theorem of align
= bar <$> (str <$> xs ∩ (ys ∪ zs)) ∪ (fst <$> zs ∩ (ys ∪ zs))
-- Absorption + commutativity of align
= bar <$> (str <$> xs ∩ (ys ∪ zs)) ∪ zs
-- Lemma(1)
= bar <$> (bimap swap fst . distrPairThese . swap <$> xs ∩ (ys ∪ zs)) ∪ zs
-- Commutativity of zip
= bar <$> (bimap swap fst . distrPairThese <$> (ys ∪ zs) ∩ xs) ∪ zs
-- Apply Distr(2)
= bar <$> (bimap swap fst <$> (ys ∩ xs) ∪ (zs ∩ xs)) ∪ zs
-- Free theorem of zip
= bar <$> ((swap <$> ys ∩ xs) ∪ (fst <$> zs ∩ xs)) ∪ zs
-- Commutativity of zip
= bar <$> ((xs ∩ ys) ∪ (fst <$> zs ∩ xs)) ∪ zs
= second rightBias . assoc <$> ((xs ∩ ys) ∪ (fst <$> zs ∩ xs)) ∪ zs
-- Associativity of align
= second rightBias <$> (xs ∩ ys) ∪ ((fst <$> zs ∩ xs) ∪ zs)
-- Free theorem of align
= (xs ∩ ys) ∪ (rightBias <$> (fst <$> zs ∩ xs) ∪ zs)
-- Commutativity
= (xs ∩ ys) ∪ (rightBias . swap <$> zs ∪ (fst <$> zs ∩ xs))
-- Lemma(2)
= (xs ∩ ys) ∪ (leftBias <$> zs ∪ (fst <$> zs ∩ xs))
-- Free theorem of align
= (xs ∩ ys) ∪ (leftBias . second fst <$> zs ∪ (zs ∩ xs))
-- Lemma(3)
= (xs ∩ ys) ∪ (leftBias . second fst . toThis <$> zs ∪ (zs ∩ xs))
-- Absorption law
= (xs ∩ ys) ∪ (leftBias . second fst . This <$> zs)
= (xs ∩ ys) ∪ (leftBias . This <$> zs)
= (xs ∩ ys) ∪ zs
-- The LHS of Distr(1)
```
