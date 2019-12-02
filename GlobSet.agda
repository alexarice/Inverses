{-# OPTIONS --without-K --safe --sized-types #-}

module GlobSet where
open import Agda.Builtin.Size public

record GlobSet (i : Size) : Set₁ where
  coinductive
  field
    cells : Set
    morphisms : (j : Size< i) → cells → cells → GlobSet j

open GlobSet public

record GlobSetMorphism {i : Size} (G H : GlobSet i) : Set where
  coinductive
  field
    func : cells G → cells H
    funcMorphisms : (j : Size< i) → (x y : cells G) → GlobSetMorphism (morphisms G j x y) (morphisms H j (func x) (func y))

open GlobSetMorphism public

idMorph : ∀{i} → (G : GlobSet i) → GlobSetMorphism G G
func (idMorph G) x = x
funcMorphisms (idMorph G) j x y = idMorph (morphisms G j x y)

gComp : ∀{i} → {G H I : GlobSet i} → GlobSetMorphism H I → GlobSetMorphism G H → GlobSetMorphism G I
func (gComp ϕ ψ) x = func ϕ (func ψ x)
funcMorphisms (gComp ϕ ψ) j x y = gComp (funcMorphisms ϕ j (func ψ x) (func ψ y)) (funcMorphisms ψ j x y)
