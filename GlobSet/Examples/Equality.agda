{-# OPTIONS --safe --without-K --sized-types #-}

module GlobSet.Examples.Equality where
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import Relation.Binary.PropositionalEquality.Core

equality : (i : Size) → Set → GlobSet i
cells (equality i A) = A
morphisms (equality i A) j x y = equality j (x ≡ y)

compEquality : ∀{i} → (S : Set) → Composable i (equality i S)
Composable.id (compEquality S) j x = refl
Composable.comp (compEquality {i} S) j x y z = γ
 where
  γ : GlobSetMorphism (morphisms (equality i S) j x y
                       ×G
                       morphisms (equality i S) j y z)
                      (morphisms (equality i S) j x z)
  func γ (refl , refl) = refl
  funcMorphisms γ j (f , g) (f' , g') = γ₂ (x ≡ y) (y ≡ z) (x ≡ z) f f' g g' (func γ)
   where
    γ₂ : {k : Size}
       → (A B C : Set)
       → (f f' : A)
       → (g g' : B)
       → (F : A × B → C)
       → GlobSetMorphism (equality k (f ≡ f') ×G equality k (g ≡ g'))
                         (equality k (F (f , g) ≡ F (f' , g')))
    func (γ₂ A B C f f' g g' F) (refl , refl) = refl
    funcMorphisms (γ₂ A B C f f' g g' F) j (α , β) (α' , β') =
      γ₂ (f ≡ f')
         (g ≡ g')
         (F (f , g) ≡ F (f' , g'))
         α
         α'
         β
         β'
         (func (γ₂ A B C f f' g g' F))
Composable.compHigher (compEquality S) j x y = compEquality (x ≡ y)
