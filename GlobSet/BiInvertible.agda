{-# OPTIONS --without-K #-}

module GlobSet.BiInvertible where

open import GlobSet
open import GlobSet.Descendant
open import GlobSet.Composition

record BiInvertible {h i : Size}
                    {G : GlobSet h}
                    (c : Composable G)
                    (j : Size< i)
                    (d : Descendant G i)
                    {x y : cells (realise d)}
                    (f : cells (morphisms (realise d) j x y)) : Set₁ where
  coinductive
  field
    f* : cells (morphisms (realise d) j y x)
    *f : cells (morphisms (realise d) j y x)
    fR : (k : Size< j) → cells (morphisms (morphisms (realise d) j x x) k (comp1 c d f f*) (idd c d j x))
    fL : (k : Size< j) → cells (morphisms (morphisms (realise d) j y y) k (comp1 c d *f f) (idd c d j y))
    fRBiInv : (k : Size< j) → BiInvertible c k (Child d j x x) (fR k)
    fLBiInv : (k : Size< j) → BiInvertible c k (Child d j y y) (fL k)

open BiInvertible public
