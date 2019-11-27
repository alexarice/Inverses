{-# OPTIONS --without-K --safe --guardedness #-}

module Inverses3 where
open import Data.Product
open import Agda.Builtin.Unit
open import Relation.Binary.PropositionalEquality.Core

record GlobSet : Set₁ where
  coinductive
  field
    cells : Set
    morphisms : cells → cells → GlobSet

open GlobSet

record GlobSetMorphism (G H : GlobSet) : Set where
  coinductive
  field
    func : cells G → cells H
    funcMorphisms : (x y : cells G) → GlobSetMorphism (morphisms G x y) (morphisms H (func x) (func y))

open GlobSetMorphism

infixr 2 _×G_

_×G_ : (G H : GlobSet) → GlobSet
cells (G ×G H) = cells G × cells H
morphisms (G ×G H) (w , x) (y , z) = morphisms G w y ×G morphisms H x z

record Composable (G : GlobSet) : Set where
  coinductive
  field
    comp : (x y z : cells G) → GlobSetMorphism (morphisms G y z ×G morphisms G x y) (morphisms G x z)
    compHigher : (x y : cells G) → Composable (morphisms G x y)
  comp1 : {x y z : cells G} → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)
  comp1 {x} {y} {z} g f = func (comp x y z) (g , f)
  comp2 : {x y z : cells G} {g g' : cells (morphisms G y z)} {f f' : cells (morphisms G x y)} → cells (morphisms (morphisms G y z) g g') → cells (morphisms (morphisms G x y) f f') → cells (morphisms (morphisms G x z) (comp1 g f) (comp1 g' f'))
  comp2 {x} {y} {z} {g} {g'} {f} {f'} α β = func (funcMorphisms (comp x y z) (g , f) (g' , f')) (α , β)

open Composable {{...}}

record Identities (G : GlobSet) : Set where
  coinductive
  field
    id : (x : cells G) → cells (morphisms G x x)
    idHigher : (x y : cells G) → Identities (morphisms G x y)

open Identities {{...}}


terminal : GlobSet
cells terminal = ⊤
morphisms terminal _ _ = terminal

idTerminal : Identities terminal
Identities.id idTerminal x = tt
Identities.idHigher idTerminal x y = idTerminal

compTerminal : Composable terminal
Composable.comp compTerminal x y z = γ
 where
  γ : GlobSetMorphism (terminal ×G terminal) terminal
  func γ (f , g) = tt
  funcMorphisms γ (f , g) (f' , g') = γ
Composable.compHigher compTerminal x y = compTerminal

equality : Set → GlobSet
cells (equality A) = A
morphisms (equality A) x y = equality (x ≡ y)

idEquality : (S : Set) → Identities (equality S)
Identities.id (idEquality S) x = refl
Identities.idHigher (idEquality S) x y = idEquality (x ≡ y)

compEquality : (S : Set) → Composable (equality S)
Composable.comp (compEquality S) x y z = γ
 where
  γ : GlobSetMorphism
        (morphisms (equality S) y z ×G morphisms (equality S) x y)
        (morphisms (equality S) x z)
  func γ (refl , refl) = refl
  funcMorphisms γ (f , g) (f' , g') = γ₂ (y ≡ z) (x ≡ y) (x ≡ z) f f' g g' (func γ)
   where
    helper : (A B C : Set) → (f f' : A) → (g g' : B) → (F : A × B → C) → cells (equality (f ≡ f') ×G equality (g ≡ g')) → cells (equality (F (f , g) ≡ F (f' , g')))
    helper A B C f .f g .g F (refl , refl) = refl
    γ₂ : (A B C : Set) → (f f' : A) → (g g' : B) → (F : A × B → C) → GlobSetMorphism (equality (f ≡ f') ×G equality (g ≡ g')) (equality (F (f , g) ≡ F (f' , g')))
    func (γ₂ A B C f f' g g' F) = helper A B C f f' g g' F
    funcMorphisms (γ₂ A B C f f' g g' F) (α , β) (α' , β') = γ₂ (f ≡ f') (g ≡ g') (F (f , g) ≡ F (f' , g')) α α' β β' (helper A B C f f' g g' F)
Composable.compHigher (compEquality S) x y = compEquality (x ≡ y)

record BiInvertible {G : GlobSet} {{_ : Composable G}} {{_ : Identities G}} {x y : cells G} (f : cells (morphisms G x y)) : Set₁ where
  coinductive
  field
    f* : cells (morphisms G y x)
    *f : cells (morphisms G y x)
    fR : cells (morphisms (morphisms G y y) (comp1 f f*) (id y))
    fL : cells (morphisms (morphisms G x x) (comp1 *f f) (id x))
    fRBiInv : BiInvertible {morphisms G y y} {{compHigher y y}} {{idHigher y y}} fR
    fLBiInv : BiInvertible {morphisms G x x} {{compHigher x x}} {{idHigher x x}} fL
