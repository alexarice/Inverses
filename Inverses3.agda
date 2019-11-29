{-# OPTIONS --without-K --safe --sized-types #-}

module Inverses3 where
open import Data.Product
open import Data.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Size
open import Relation.Binary.PropositionalEquality.Core

record GlobSet (i : Size) : Set₁ where
  coinductive
  field
    cells : Set
    morphisms : ∀{j : Size< i} → cells → cells → GlobSet j

open GlobSet

record GlobSetMorphism {i : Size} (G H : GlobSet i) : Set where
  coinductive
  field
    func : cells G → cells H
    funcMorphisms : ∀{j : Size< i} → (x y : cells G) → GlobSetMorphism (morphisms G x y) (morphisms H (func x) (func y))

open GlobSetMorphism

idMorph : ∀{i} → (G : GlobSet i) → GlobSetMorphism G G
func (idMorph G) x = x
funcMorphisms (idMorph G) x y = idMorph (morphisms G x y)

gComp : ∀{i} → {G H I : GlobSet i} → GlobSetMorphism H I → GlobSetMorphism G H → GlobSetMorphism G I
func (gComp ϕ ψ) x = func ϕ (func ψ x)
funcMorphisms (gComp ϕ ψ) x y = gComp (funcMorphisms ϕ (func ψ x) (func ψ y)) (funcMorphisms ψ x y)

infixr 2 _×G_

_×G_ : ∀ {i} → (G H : GlobSet i) → GlobSet i
cells (G ×G H) = cells G × cells H
morphisms (G ×G H) (w , x) (y , z) = morphisms G w y ×G morphisms H x z

infixr 3 _×GM_

_×GM_ : ∀ {i} {G H I J : GlobSet i} → GlobSetMorphism G H → GlobSetMorphism I J → GlobSetMorphism (G ×G I) (H ×G J)
func (ϕ ×GM ψ) (x , y) = (func ϕ x) , (func ψ y)
funcMorphisms (ϕ ×GM ψ) (x , y) (x' , y') = (funcMorphisms ϕ x x') ×GM funcMorphisms ψ y y'

record Composable {i : Size} (G : GlobSet i) : Set where
  coinductive
  field
    id : ∀ {j : Size< i} → (x : cells G) → cells (morphisms G x x)
    comp : ∀{j : Size< i} → (x y z : cells G) → GlobSetMorphism (morphisms G y z ×G morphisms G x y) (morphisms G x z)
    compHigher : ∀{j : Size< i} → (x y : cells G) → Composable (morphisms G x y)
  comp1 : ∀{j : Size< i} {x y z : cells G} → cells (morphisms G {j} y z) → cells (morphisms G {j} x y) → cells (morphisms G {j} x z)
  comp1 {_} {x} {y} {z} g f = func (comp x y z) (g , f)
  comp2 : ∀{j : Size< i} {h : Size< j} {x y z : cells G} {g g' : cells (morphisms G y z)} {f f' : cells (morphisms G x y)} → cells (morphisms (morphisms G y z) g g') → cells (morphisms (morphisms G x y) f f') → cells (morphisms (morphisms G x z) (comp1 g f) (comp1 g' f'))
  comp2 {_} {_} {x} {y} {z} {g} {g'} {f} {f'} α β = func (funcMorphisms (comp x y z) (g , f) (g' , f')) (α , β)
  comp3 : ∀{j : Size< i} {h : Size< j} {k : Size< h} {x y z : cells G} {g g' : cells (morphisms G y z)} {f f' : cells (morphisms G x y)} → {α α' : cells (morphisms (morphisms G y z) g g')} → {β β' : cells (morphisms (morphisms G x y) f f')} → cells (morphisms (morphisms (morphisms G y z) g g') α α') → cells (morphisms (morphisms (morphisms G x y) f f') β β') → cells (morphisms (morphisms (morphisms G x z) (comp1 g f) (comp1 g' f')) (comp2 α β) (comp2 α' β'))
  comp3 {_} {_} {_} {x} {y} {z} {g} {g'} {f} {f'} {α} {α'} {β} {β'} δ ε = func (funcMorphisms (funcMorphisms (comp x y z) (g , f) (g' , f')) (α , β) (α' , β')) (δ , ε)

open Composable {{...}}

terminal : (i : Size) → GlobSet i
cells (terminal i)= ⊤
morphisms (terminal i) {j} _ _ = terminal j

compTerminal : ∀{i} → Composable (terminal i)
Composable.id compTerminal x = tt
Composable.comp compTerminal x y z = γ
 where
  γ : {j : Size} → GlobSetMorphism (terminal j ×G terminal j) (terminal j)
  func γ (f , g) = tt
  funcMorphisms γ (f , g) (f' , g') = γ
Composable.compHigher compTerminal x y = compTerminal

equality : (i : Size) → Set → GlobSet i
cells (equality i A) = A
morphisms (equality i A) {j} x y = equality j (x ≡ y)

compEquality : ∀{i} → (S : Set) → Composable (equality i S)
Composable.id (compEquality S) x = refl
Composable.comp (compEquality S) {j} x y z = γ
 where
  γ : GlobSetMorphism {j}
        (morphisms (equality (↑ j) S) y z ×G morphisms (equality (↑ j) S) x y)
        (morphisms (equality (↑ j) S) x z)
  func γ (refl , refl) = refl
  funcMorphisms γ (f , g) (f' , g') = γ₂ (y ≡ z) (x ≡ y) (x ≡ z) f f' g g' (func γ)
   where
    γ₂ : {k : Size} (A B C : Set) → (f f' : A) → (g g' : B) → (F : A × B → C) → GlobSetMorphism {k} (equality k (f ≡ f') ×G equality k (g ≡ g')) (equality k (F (f , g) ≡ F (f' , g')))
    func (γ₂ A B C f f' g g' F) (refl , refl) = refl
    funcMorphisms (γ₂ A B C f f' g g' F) (α , β) (α' , β') = γ₂ (f ≡ f') (g ≡ g') (F (f , g) ≡ F (f' , g')) α α' β β' (func (γ₂ A B C f f' g g' F))
Composable.compHigher (compEquality S) x y = compEquality (x ≡ y)

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
