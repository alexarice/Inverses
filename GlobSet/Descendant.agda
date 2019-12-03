{-# OPTIONS --without-K #-}

module GlobSet.Descendant where

open import GlobSet
open import Data.Product

data Descendant {i : Size} (G : GlobSet i) : (j : Size) → Set

realise : {i j : Size} → {G : GlobSet i} → Descendant G j → GlobSet j

data Descendant {i} G where
  Orig : Descendant G i
  Child : {j : Size} → (d : Descendant G j) → (k : Size< j) → (x y : cells (realise d)) → Descendant G k

realise {_} {_} {G} Orig = G
realise (Child d k x y) = morphisms (realise d) k x y
