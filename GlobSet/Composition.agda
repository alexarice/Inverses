{-# OPTIONS --without-K --safe --sized-types #-}

module GlobSet.Composition where
open import GlobSet
open import GlobSet.Product

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

open Composable {{...}} public
