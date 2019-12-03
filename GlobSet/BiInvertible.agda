{-# OPTIONS --without-K #-}

module GlobSet.BiInvertible where

open import GlobSet
open import GlobSet.Descendant
open import GlobSet.Composition

record BiInvertible {i : Size} (j : Size< i) (G : GlobSet i) {{_ : Composable G}} {x y : cells G} (f : cells (morphisms G j x y)) : Set₁ where
  coinductive
  field
    f* : cells (morphisms G j y x)
    *f : cells (morphisms G j y x)
    fR : (k : Size< j) → cells (morphisms (morphisms G j y y) k (comp1 Orig f f*) (id j y))
    fL : (k : Size< j) → cells (morphisms (morphisms G j x x) k (comp1 Orig *f f) (id j x))
    fRBiInv : (k : Size< j) → BiInvertible k (morphisms G j y y) {{compHigher j y y}} (fR k)
    fLBiInv : (k : Size< j) → BiInvertible k (morphisms G j x x) {{compHigher j x x}} (fL k)

open BiInvertible public
