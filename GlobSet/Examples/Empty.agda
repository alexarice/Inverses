{-# OPTIONS --without-K --sized-types --safe #-}

module GlobSet.Examples.Empty where

open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.Invertible
open import GlobSet.HCat
open import Data.Empty

emptyGlobSet : (i : Size) → GlobSet 0ℓ i
emptyGlobSet i .cells = ⊥
emptyGlobSet i .morphisms _ x = ⊥-elim x

compEmpty : (i : Size) → Composable i (emptyGlobSet i)
compEmpty i .id _ x = ⊥-elim x
compEmpty i .comp _ x = ⊥-elim x
compEmpty i .compHigher _ x = ⊥-elim x

hCatEmpty : (i : Size) → HCat (emptyGlobSet i) (compEmpty i)
hCatEmpty i .compPreserveId _ x = ⊥-elim x
hCatEmpty i .compPreserveComp _ x = ⊥-elim x
hCatEmpty i .ƛ _ {x} = ⊥-elim x
hCatEmpty i .ρ _ {x} = ⊥-elim x
hCatEmpty i .assoc {x = x} = ⊥-elim x
hCatEmpty i .hcoin _ x = ⊥-elim x
