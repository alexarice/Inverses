{-# OPTIONS --without-K --sized-types #-}

module Inverses3 where
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible
open import GlobSet.HCat


idIsBiInv : ∀{i} {j : Size< i} {k : Size< j} {G : GlobSet i} {{_ : Composable G}} {{_ : HCat G}} → (x : cells G) → BiInvertible G (id x)
f* (idIsBiInv x) = id x
*f (idIsBiInv x) = id x
fR (idIsBiInv x) = ƛ (id x)
fL (idIsBiInv x) = ƛ (id x)
fRBiInv (idIsBiInv x) = ƛBiInv (id x)
fLBiInv (idIsBiInv x) = ƛBiInv (id x)

record BiInvertComp {i : Size} {j : Size< i} {A B C : GlobSet i} {{_ : Composable A}} {{_ : Composable B}} {{_ : Composable C}} {x x' : cells A} {y y' : cells B} {z z' : cells C} (composition : GlobSetMorphism (morphisms A x x' ×G morphisms B y y') (morphisms C z z')) : Set₁ where
  coinductive
  field
    biComp : {k : Size< j} {f : cells (morphisms A x x')} {g : cells (morphisms B y y')} → BiInvertible A f → BiInvertible B g → BiInvertible C (func composition (f , g))
    biCompHigher : {k : Size< j} (f f' : cells (morphisms A x x')) → (g g' : cells (morphisms B y y')) → BiInvertComp {{compHigher x x'}} {{compHigher y y'}} {{compHigher z z'}} (funcMorphisms composition (f , g) (f' , g'))

open BiInvertComp

compBiInv : {i : Size} {j : Size< i} {G : GlobSet i} {{_ : Composable G}} {{_ : HCat G}} (x y z : cells G) → BiInvertComp (comp x y z)
biComp (compBiInv x y z) = {!!}
f* (biComp (biCompHigher (compBiInv x y z) f f' g g') bα bβ) = func (funcMorphisms (comp x y z) (f' , g') (f , g)) ((f* ⦃ compHigher y z ⦄ bα) , (f* ⦃ compHigher x y ⦄ bβ))
*f (biComp (biCompHigher (compBiInv x y z) f f' g g') bα bβ) = func (funcMorphisms (comp x y z) (f' , g') (f , g)) ((*f ⦃ compHigher y z ⦄ bα) , *f ⦃ compHigher x y ⦄ bβ)
fR (biComp (biCompHigher (compBiInv x y z) f f' g g') bα bβ) = {!!}
fL (biComp (biCompHigher (compBiInv x y z) f f' g g') bα bβ) = {!!}
fRBiInv (biComp (biCompHigher (compBiInv x y z) f f' g g') bα bβ) = {!!}
fLBiInv (biComp (biCompHigher (compBiInv x y z) f f' g g') bα bβ) = {!!}
biCompHigher (biCompHigher (compBiInv x y z) f f' g g') = {!!}
