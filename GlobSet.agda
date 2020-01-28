{-# OPTIONS --without-K --safe --sized-types #-}

module GlobSet where
open import Agda.Builtin.Size public
open import Level public

record GlobSet (a : Level) (i : Size) : Set (suc a)  where
  coinductive
  field
    cells : Set a
    morphisms : (j : Size< i) → cells → cells → GlobSet a j

open GlobSet public

record GlobSetMorphism {a b : Level} {i : Size} (G : GlobSet a i) (H : GlobSet b i) : Set (a ⊔ b) where
  coinductive
  field
    func : cells G → cells H
    funcMorphisms : (j : Size< i)
                  → (x y : cells G)
                  → GlobSetMorphism (morphisms G j x y)
                                    (morphisms H j (func x) (func y))

open GlobSetMorphism public

idMorph : {a : Level} {i : Size} → (G : GlobSet a i) → GlobSetMorphism G G
idMorph G .func x = x
idMorph G .funcMorphisms j x y = idMorph (morphisms G j x y)

gComp : {a b c : Level} {i : Size} {G : GlobSet a i} {H : GlobSet b i} {I : GlobSet c i} → GlobSetMorphism H I → GlobSetMorphism G H → GlobSetMorphism G I
gComp ϕ ψ .func x = func ϕ (func ψ x)
gComp ϕ ψ .funcMorphisms j x y = gComp (funcMorphisms ϕ j (func ψ x) (func ψ y)) (funcMorphisms ψ j x y)
