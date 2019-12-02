{-# OPTIONS --without-K #-}

module GlobSet.HCat where

open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible

record SameMorphism {i : Size} {G H : GlobSet i} ⦃ _ : Composable G ⦄ ⦃ _ : Composable H ⦄ (F₁ F₂ : GlobSetMorphism G H) : Set₁ where
  coinductive
  field
    eq : (j : Size< i) → (x : cells G) → cells (morphisms H j (func F₁ x) (func F₂ x))
    eqBiInv : (j : Size< i) → (x : cells G) → BiInvertible j H (eq j x)

record PreserveIden {i : Size} {G H : GlobSet i} ⦃ _ : Composable G ⦄ ⦃ _ : Composable H ⦄ (F : GlobSetMorphism G H) : Set₁ where
  coinductive
  field
    idPreserve : (j : Size< i) → (k : Size< j) → (x : cells G) → cells (morphisms (morphisms H j (func F x) (func F x)) k (func (funcMorphisms F j x x) (id j x)) (id j (func F x)))
    idPreserveBiInv : (j : Size< i) → (k : Size< j) → (x : cells G) → BiInvertible k (morphisms H j (func F x) (func F x)) ⦃ compHigher j (func F x) (func F x) ⦄ (idPreserve j k x)
    idPreserveCoin : (j : Size< i) → (x y : cells G) → PreserveIden ⦃ compHigher j x y ⦄ ⦃ compHigher j (func F x) (func F y) ⦄ (funcMorphisms F j x y)

record PreserveComp {i : Size} {G H : GlobSet i} ⦃ _ : Composable G ⦄ ⦃ _ : Composable H ⦄ (F : GlobSetMorphism G H) : Set₁ where
  coinductive
  field
    compPreserve : (j : Size< i) → (k : Size< j) → (x y z : cells G) → SameMorphism ⦃ prodComp (morphisms G j y z) (morphisms G j x y) ⦃ compHigher j y z ⦄ ⦃ compHigher j x y ⦄ ⦄ ⦃ compHigher j (func F x) (func F z) ⦄ (gComp (comp j (func F x) (func F y) (func F z)) (funcMorphisms F j y z ×GM funcMorphisms F j x y)) (gComp (funcMorphisms F j x z) (comp j x y z))
    compPreserveCoin : (j : Size< i) → (x y : cells G) → PreserveComp ⦃ compHigher j x y ⦄ ⦃ compHigher j (func F x) (func F y) ⦄ (funcMorphisms F j x y)

record HCat {i : Size} (G : GlobSet i) ⦃ _ : Composable G ⦄ : Set₁ where
  coinductive
  field
    compPreserveId : (j : Size< i) → {x y z : cells G} → PreserveIden ⦃ prodComp (morphisms G j y z) (morphisms G j x y) ⦃ compHigher j y z ⦄ ⦃ compHigher j x y ⦄ ⦄ ⦃ compHigher j x z ⦄ (comp j x y z)
    ƛ : {j : Size< i} → (k : Size< j) → {x y : cells G} → (f : cells (morphisms G j x y)) → cells (morphisms (morphisms G j x y) k (comp1 (id j y) f) f)
    ƛBiInv : {j : Size< i} → (k : Size< j) → {x y : cells G} → (f : cells (morphisms G j x y)) → BiInvertible k (morphisms G j x y) ⦃ compHigher j x y ⦄ (ƛ k f)
    compPreserveComp : (j : Size< i) → (x y z : cells G) → PreserveComp ⦃ prodComp (morphisms G j y z) (morphisms G j x y) ⦃ compHigher j y z ⦄ ⦃ compHigher j x y ⦄ ⦄ ⦃ compHigher j x z ⦄ (comp j x y z)
    hcoin : (j : Size< i) → (x y : cells G) → HCat (morphisms G j x y) ⦃ compHigher j x y ⦄
  interchange₁ : {!!}
  interchange₁ = ?

open HCat ⦃ ... ⦄ public
