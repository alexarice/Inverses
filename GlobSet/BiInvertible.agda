{-# OPTIONS --without-K #-}

module GlobSet.BiInvertible where

open import GlobSet
open import GlobSet.Descendant
open import GlobSet.Composition

record BiInvertible {h i : Size}
                    {G : GlobSet h}
                    ⦃ _ : Composable G ⦄
                    (j : Size< i)
                    (d : ExDescendant G i)
                    {x y : cells (realiseEx d)}
                    (f : cells (morphisms (realiseEx d) j x y)) : Set₁ where
  coinductive
  field
    f* : cells (morphisms (realiseEx d) j y x)
    *f : cells (morphisms (realiseEx d) j y x)
    fR : (k : Size< j) → cells (morphisms (morphisms (realiseEx d) j x x) k (comp1 d f f*) (idd d j x))
    fL : (k : Size< j) → cells (morphisms (morphisms (realise d) j y y) k (comp1 d *f f) (idd d j y))
    fRBiInv : (k : Size< j) → BiInvertible k (Child d j x x) (fR k)
    fLBiInv : (k : Size< j) → BiInvertible k (Child d j y y) (fL k)

open BiInvertible public
