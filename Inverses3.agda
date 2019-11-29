{-# OPTIONS --without-K --safe --sized-types #-}

module Inverses3 where
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition


prodComp : ∀{i} → (A B : GlobSet i) {{_ : Composable A}} {{_ : Composable B}} → Composable (A ×G B)
Composable.id (prodComp A B) (x , y) = (id x) , (id y)
func (Composable.comp (prodComp A B) (x , x') (y , y') (z , z')) ((f , f') , (g , g')) = func (comp x y z) (f , g) , func (comp x' y' z') (f' , g')
funcMorphisms (Composable.comp (prodComp A B) (x , x') (y , y') (z , z')) ((f₁ , f₁') , (g₁ , g₁')) ((f₂ , f₂') , (g₂ , g₂')) = {!!}
Composable.compHigher (prodComp A B) (x , x') (y , y') = prodComp (morphisms A x y) (morphisms B x' y') ⦃ compHigher x y ⦄ ⦃ compHigher x' y' ⦄

record BiInvertible {i : Size} {j : Size< i} {k : Size< j} (G : GlobSet i) {{_ : Composable G}} {x y : cells G} (f : cells (morphisms G x y)) : Set₁ where
  coinductive
  field
    f* : cells (morphisms G y x)
    *f : cells (morphisms G y x)
    fR : cells (morphisms (morphisms G y y) (comp1 f f*) (id y))
    fL : cells (morphisms (morphisms G x x) (comp1 *f f) (id x))
    fRBiInv : ∀ {l : Size< k} → BiInvertible (morphisms G y y) {{compHigher y y}} fR
    fLBiInv : ∀ {l : Size< k} → BiInvertible (morphisms G x x) {{compHigher x x}} fL

open BiInvertible

record HCat {i : Size} (G : GlobSet i) {{_ : Composable G}} : Set₁ where
  coinductive
  field
    ƛ : {j : Size< i} {k : Size< j} {x y : cells G} → (f : cells (morphisms {i} G {j} x y)) → cells (morphisms (morphisms G {j} x y) {k} (comp1 (id y) f) f)
    ƛBiInv : {j : Size< i} {k : Size< j} {l : Size< k} {x y : cells G} → (f : cells (morphisms G {j} x y)) → BiInvertible (morphisms G x y) {{compHigher x y}} (ƛ f)
    hcoin : {j : Size< i} → (x y : cells G) → HCat (morphisms G x y) {{compHigher x y}}

open HCat {{...}}

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
