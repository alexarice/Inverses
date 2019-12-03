{-# OPTIONS --without-K #-}

module GlobSet.Descendant where

open import GlobSet
open import GlobSet.Product

data Descendant {i : Size} (G : GlobSet i) : (j : Size) → Set

realise : {i j : Size} → {G : GlobSet i} → Descendant G j → GlobSet j

data Descendant {i} G where
  Orig : Descendant G i
  Child : {j : Size} → (d : Descendant G j) → (k : Size< j) → (x y : cells (realise d)) → Descendant G k
  Prod : {j : Size} → (d₁ d₂ : Descendant G j) → Descendant G j

realise {_} {_} {G} Orig = G
realise (Child d k x y) = morphisms (realise d) k x y
realise (Prod d₁ d₂) = (realise d₁) ×G (realise d₂)
