{-# OPTIONS --safe --without-K --sized-types #-}

module GlobSet.Examples.Equality where
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible
open import GlobSet.HCat
open import Relation.Binary.PropositionalEquality.Core

equality : (i : Size) → Set → GlobSet i
cells (equality i A) = A
morphisms (equality i A) j x y = equality j (x ≡ y)

equalityCompHelper₂ : {k : Size}
       → {A B C : Set}
       → (f f' : A)
       → (g g' : B)
       → (F : A × B → C)
       → GlobSetMorphism (equality k (f ≡ f') ×G equality k (g ≡ g'))
                         (equality k (F (f , g) ≡ F (f' , g')))
func (equalityCompHelper₂ f .f g .g F) (refl , refl) = refl
funcMorphisms (equalityCompHelper₂ f f' g g' F) j (α , β) (α' , β') =
  equalityCompHelper₂ α
                      α'
                      β
                      β'
                      (func (equalityCompHelper₂ f f' g g' F))

equalityCompHelper : (i : Size)
                   → (S : Set)
                   → (j : Size< i)
                   → (x y z : S)
                   → GlobSetMorphism (morphisms (equality i S) j x y
                                      ×G
                                      morphisms (equality i S) j y z)
                                     (morphisms (equality i S) j x z)
func (equalityCompHelper i S j x y z) (f , g) = trans f g
funcMorphisms (equalityCompHelper i S j x y z) k (f , g) (f' , g') =
  equalityCompHelper₂ f f' g g' (func (equalityCompHelper i S j x y z))



compEquality : (i : Size) → (S : Set) → Composable i (equality i S)
Composable.id (compEquality i S) j x = refl
Composable.comp (compEquality i S) j x y z = equalityCompHelper i S j x y z

Composable.compHigher (compEquality i S) j x y = compEquality j (x ≡ y)

equalityInvertibleMorphisms : (i : Size)
                            → (S : Set)
                            → (j : Size< i)
                            → {x y : S}
                            → (p : x ≡ y)
                            → BiInvertible i (compEquality i S) j p
f* (equalityInvertibleMorphisms i S j refl) = refl
*f (equalityInvertibleMorphisms i S j refl) = refl
fR (equalityInvertibleMorphisms i S j refl) k = refl
fL (equalityInvertibleMorphisms i S j refl) k = refl
fRBiInv (equalityInvertibleMorphisms i S j {x} refl) k = equalityInvertibleMorphisms j (x ≡ x) k refl
fLBiInv (equalityInvertibleMorphisms i S j {x} refl) k = equalityInvertibleMorphisms j (x ≡ x) k refl

hCatEquality : (i : Size) → (S : Set) → HCat (equality i S) (compEquality i S)
idPreserve (compPreserveId (hCatEquality i S) j x y z) k l w = refl
idPreserveBiInv (compPreserveId (hCatEquality i S) j x .x .x) k l (refl , refl) = equalityInvertibleMorphisms k (refl ≡ refl) l refl
idPreserveCoin (compPreserveId (hCatEquality i S) j x y z) k (a , b) (c , d) = γ j k (λ v → trans (proj₁ v) (proj₂ v)) a c b d
 where
  γ : (j : Size)
    → (k : Size< j)
    → {A B C : Set}
    → (t : A × B → C)
    → (a c : A)
    → (b d : B)
    → PreserveIden (prodComp (compEquality k (a ≡ c))
                             (compEquality k (b ≡ d)))
                   (compEquality k (t (a , b) ≡ t (c , d)))
                   (equalityCompHelper₂ a c b d t)
  idPreserve (γ j k t a c b d) l m w = refl
  idPreserveBiInv (γ j k t a c b d) l m (refl , refl) = equalityInvertibleMorphisms l (refl ≡ refl) m refl
  idPreserveCoin (γ j k {S} t a c b d) l (e , f) (g , h) = γ k l (func (equalityCompHelper₂ a c b d t)) e g f h
eq (compPreserve (compPreserveComp (hCatEquality i S) j x y z) k l (a , b) (.a , .b) (.a , .b)) m ((refl , refl) , (refl , refl)) = refl
eqBiInv (compPreserve (compPreserveComp (hCatEquality i S) j _ _ _) k l (refl , refl) (.refl , .refl) (.refl , .refl)) m ((refl , refl) , refl , refl) = equalityInvertibleMorphisms k (refl ≡ refl) m refl
compPreserveCoin (compPreserveComp (hCatEquality i S) j x y z) k (a , b) (c , d) = γ j k (λ {(v₁ , v₂) → trans v₁ v₂}) a c b d
 where
  γ : (j : Size)
    → (k : Size< j)
    → {A B C : Set}
    → (t : A × B → C)
    → (a c : A)
    → (b d : B)
    → PreserveComp (prodComp (compEquality k (a ≡ c))
                             (compEquality k (b ≡ d)))
                   (compEquality k (t (a , b) ≡ t (c , d)))
                   (equalityCompHelper₂ a c b d t)
  eq (compPreserve (γ j k t a .a b .b) l m (refl , refl) (.refl , .refl) (.refl , .refl)) n ((refl , refl) , refl , refl) = refl
  eqBiInv (compPreserve (γ j k t a .a b .b) l m (refl , refl) (.refl , .refl) (.refl , .refl)) n ((refl , refl) , refl , refl) = equalityInvertibleMorphisms l (refl ≡ refl) n refl
  compPreserveCoin (γ j k t a c b d) l (w , x) (y , z) = γ k l (func (equalityCompHelper₂ a c b d t)) w y x z
ƛ (hCatEquality i S) k refl = refl
ƛBiInv (hCatEquality i S) {j} k {x} refl = equalityInvertibleMorphisms j (x ≡ x) k refl
assoc (hCatEquality i S) refl refl refl refl = refl
assocBiInv (hCatEquality i S) {j} {k} {x} refl refl refl refl = equalityInvertibleMorphisms j (x ≡ x) k (assoc (hCatEquality i S) refl refl refl refl)
hcoin (hCatEquality i S) j x y = hCatEquality j (x ≡ y)
