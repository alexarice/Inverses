{-# OPTIONS --without-K --sized-types --safe #-}

module GlobSet.BiInvertible.Core where

open import GlobSet
open import GlobSet.Composition

record BiInvertible {a : Level}
                    (i : Size)
                    {G : GlobSet a i}
                    (c : Composable i G)
                    (j : Size< i)
                    {x y : cells G}
                    (f : cells (morphisms G j x y)) : Set (suc a)

record BiInvertibleCell {a : Level}
                        (i : Size)
                        {G : GlobSet a i}
                        (c : Composable i G)
                        (j : Size< i)
                        (x y : cells G) : Set (suc a) where
  coinductive
  field
    cell : cells (morphisms G j x y)
    biInv : BiInvertible i c j cell

record BiInvertible {a} i {G} c j {x} {y} f where
  coinductive
  field
    f* : cells (morphisms G j y x)
    *f : cells (morphisms G j y x)
    fR : (k : Size< j) → BiInvertibleCell j (compHigher c j x x) k (comp1 c f f*) (id c j x)
    fL : (k : Size< j) → BiInvertibleCell j (compHigher c j y y) k (comp1 c *f f) (id c j y)

open BiInvertibleCell public
open BiInvertible public
