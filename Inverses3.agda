{-# OPTIONS --without-K --sized-types #-}

module Inverses3 where
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible
open import GlobSet.HCat


idIsBiInv : ∀{i} (j : Size< i) {G : GlobSet i} {{_ : Composable G}} {{_ : HCat G}} → (x : cells G) → BiInvertible j G (id j x)
f* (idIsBiInv j x) = id j x
*f (idIsBiInv j x) = id j x
fR (idIsBiInv j x) k = ƛ k (id j x)
fL (idIsBiInv j x) k = ƛ k (id j x)
fRBiInv (idIsBiInv j x) k = ƛBiInv k (id j x)
fLBiInv (idIsBiInv j x) k = ƛBiInv k (id j x)

record BiInvertComp {i : Size} (j : Size< i) {A B C : GlobSet i} {{_ : Composable A}} {{_ : Composable B}} {{_ : Composable C}} {x x' : cells A} {y y' : cells B} {z z' : cells C} (composition : GlobSetMorphism (morphisms A j x x' ×G morphisms B j y y') (morphisms C j z z')) : Set₁ where
  coinductive
  field
    biComp : {k : Size< j} {f : cells (morphisms A j x x')} {g : cells (morphisms B j y y')} → BiInvertible j A f → BiInvertible j B g → BiInvertible j C (func composition (f , g))
    biCompHigher : (k : Size< j) → (f f' : cells (morphisms A j x x')) → (g g' : cells (morphisms B j y y')) → BiInvertComp k {{compHigher j x x'}} {{compHigher j y y'}} {{compHigher j z z'}} (funcMorphisms composition k (f , g) (f' , g'))

open BiInvertComp

compBiInv : {i : Size} (j : Size< i) {G : GlobSet i} {{_ : Composable G}} {{_ : HCat G}} (x y z : cells G) → BiInvertComp j (comp j x y z)
biComp (compBiInv j x y z) = {!!}
f* (biComp (biCompHigher (compBiInv j x y z) k f f' g g') bα bβ) = func (funcMorphisms (comp j x y z) k (f' , g') (f , g)) ((f* ⦃ compHigher j y z ⦄ bα) , (f* ⦃ compHigher j x y ⦄ bβ))
*f (biComp (biCompHigher (compBiInv j x y z) k f f' g g') bα bβ) = func (funcMorphisms (comp j x y z) k (f' , g') (f , g)) ((*f ⦃ compHigher j y z ⦄ bα) , *f ⦃ compHigher j x y ⦄ bβ)
fR (biComp (biCompHigher (compBiInv j x y z) k f f' g g') bα bβ) = {!!}
fL (biComp (biCompHigher (compBiInv j x y z) k f f' g g') bα bβ) = {!!}
fRBiInv (biComp (biCompHigher (compBiInv j x y z) k f f' g g') bα bβ) = {!!}
fLBiInv (biComp (biCompHigher (compBiInv j x y z) k f f' g g') bα bβ) = {!!}
biCompHigher (biCompHigher (compBiInv j x y z) k f f' g g') = {!!}
