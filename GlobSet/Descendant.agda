{-# OPTIONS --without-K #-}

module GlobSet.Descendant where

open import GlobSet
open import GlobSet.Product

data Descendant {i : Size} (G : GlobSet i) : (j : Size) → Set
data ExDescendant {i : Size} (G : GlobSet i) : (j : Size) → Set

realise : {i j : Size} → {G : GlobSet i} → Descendant G j → GlobSet j
realiseEx : {i j : Size} → {G : GlobSet i} → ExDescendant G j → GlobSet j

data Descendant {i} G where
  Orig : Descendant G i
  Child : {j : Size} → (d : Descendant G j) → (k : Size< j) → (x y : cells (realise d)) → Descendant G k
--  Prod : {j : Size} → (d₁ d₂ : Descendant G j) → Descendant G j

data ExDescendant {i} G where
  OrigEx : ExDescendant G i
  ChildEx : {j : Size} → (d : ExDescendant G j) → (k : Size< j) → (x y : cells (realiseEx d)) → ExDescendant G k
  Prod : {j : Size} → (d₁ d₂ : ExDescendant G j) → ExDescendant G j

realise {_} {_} {G} Orig = G
realise (Child d k x y) = morphisms (realise d) k x y

realiseEx {G = G} OrigEx = G
realiseEx (ChildEx d k x y) = morphisms (realiseEx d) k x y
realiseEx (Prod d₁ d₂) = (realiseEx d₁) ×G (realiseEx d₂)
