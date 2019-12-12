{-# OPTIONS --without-K --sized-types --safe #-}

module GlobSet.BiInvertible where

open import GlobSet
open import GlobSet.Composition

record BiInvertible (i : Size)
                    {G : GlobSet i}
                    (c : Composable i G)
                    (j : Size< i)
                    {x y : cells G}
                    (f : cells (morphisms G j x y)) : Set₁ where
  coinductive
  field
    f* : cells (morphisms G j y x)
    *f : cells (morphisms G j y x)
    fR : (k : Size< j) → cells (morphisms (morphisms G j x x) k (comp1 c f f*) (id c j x))
    fL : (k : Size< j) → cells (morphisms (morphisms G j y y) k (comp1 c *f f) (id c j y))
    fRBiInv : (k : Size< j) → BiInvertible j (compHigher c j x x) k (fR k)
    fLBiInv : (k : Size< j) → BiInvertible j (compHigher c j y y) k (fL k)

open BiInvertible public
