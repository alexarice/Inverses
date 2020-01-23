{-# OPTIONS --without-K --sized-types --safe #-}

module GlobSet.Examples.Empty where

open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.Invertible
open import GlobSet.HCat
open import Data.Empty

emptyGlobSet : (i : Size) → GlobSet 0ℓ i
cells (emptyGlobSet i) = ⊥
morphisms (emptyGlobSet i) _ x = ⊥-elim x

compEmpty : (i : Size) → Composable i (emptyGlobSet i)
id (compEmpty i) _ x = ⊥-elim x
comp (compEmpty i) _ x = ⊥-elim x
compHigher (compEmpty i) _ x = ⊥-elim x

hCatEmpty : (i : Size) → HCat (emptyGlobSet i) (compEmpty i)
compPreserveId (hCatEmpty i) _ x = ⊥-elim x
compPreserveComp (hCatEmpty i) _ x = ⊥-elim x
ƛ (hCatEmpty i) _ {x} = ⊥-elim x
assoc (hCatEmpty i) {x = x} = ⊥-elim x
hcoin (hCatEmpty i) _ x = ⊥-elim x
