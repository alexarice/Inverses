{-# OPTIONS --safe --without-K --sized-types #-}

module GlobSet.Examples.Equality where
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible
open import GlobSet.HCat
open import Relation.Binary.PropositionalEquality.Core

equality : {a : Level} → (i : Size) → Set a → GlobSet a i
cells (equality i A) = A
morphisms (equality i A) j x y = equality j (x ≡ y)

equalityCompHelper₂ : {a : Level}
                    → {k : Size}
                    → {A B C : Set a}
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

equalityCompHelper : {a : Level}
                   → (i : Size)
                   → (S : Set a)
                   → (j : Size< i)
                   → (x y z : S)
                   → GlobSetMorphism (morphisms (equality i S) j x y
                                      ×G
                                      morphisms (equality i S) j y z)
                                     (morphisms (equality i S) j x z)
func (equalityCompHelper i S j x y z) (f , g) = trans f g
funcMorphisms (equalityCompHelper i S j x y z) k (f , g) (f' , g') =
  equalityCompHelper₂ f f' g g' (func (equalityCompHelper i S j x y z))



compEquality : {a : Level} → (i : Size) → (S : Set a) → Composable i (equality i S)
Composable.id (compEquality i S) j x = refl
Composable.comp (compEquality i S) j x y z = equalityCompHelper i S j x y z

Composable.compHigher (compEquality i S) j x y = compEquality j (x ≡ y)

equalityInvertibleMorphisms : {a : Level}
                            → (i : Size)
                            → {S : Set a}
                            → (j : Size< i)
                            → (x : S)
                            → BiInvertibleCell i (compEquality i S) j x x
cell (equalityInvertibleMorphisms i S j) = refl
f* (biInv (equalityInvertibleMorphisms i S j)) = refl
*f (biInv (equalityInvertibleMorphisms i S j)) = refl
fR (biInv (equalityInvertibleMorphisms i S j)) k = equalityInvertibleMorphisms S k refl
fL (biInv (equalityInvertibleMorphisms i S j)) k = equalityInvertibleMorphisms S k refl

hCatEquality : {a : Level} → (i : Size) → (S : Set a) → HCat (equality i S) (compEquality i S)
idPreserve (compPreserveId (hCatEquality i S) j x y z) k l w = equalityInvertibleMorphisms k l refl
idPreserveCoin (compPreserveId (hCatEquality i S) j x y z) k (a , b) (c , d) = γ j k (λ v → trans (proj₁ v) (proj₂ v)) a c b d
 where
  γ : {l : Level}
    → (j : Size)
    → (k : Size< j)
    → {A B C : Set l}
    → (t : A × B → C)
    → (a c : A)
    → (b d : B)
    → PreserveIden (prodComp (compEquality k (a ≡ c))
                             (compEquality k (b ≡ d)))
                   (compEquality k (t (a , b) ≡ t (c , d)))
                   (equalityCompHelper₂ a c b d t)
  idPreserve (γ j k t a c b d) l m w = equalityInvertibleMorphisms l m refl
  idPreserveCoin (γ j k {S} t a c b d) l (e , f) (g , h) = γ k l (func (equalityCompHelper₂ a c b d t)) e g f h
eq (compPreserve (compPreserveComp (hCatEquality i S) j x y z) k l (a , b) (.a , .b) (.a , .b)) m ((refl , refl) , (refl , refl)) = equalityInvertibleMorphisms k m refl
compPreserveCoin (compPreserveComp (hCatEquality i S) j x y z) k (a , b) (c , d) = γ j k (λ {(v₁ , v₂) → trans v₁ v₂}) a c b d
 where
  γ : {l : Level}
    → (j : Size)
    → (k : Size< j)
    → {A B C : Set l}
    → (t : A × B → C)
    → (a c : A)
    → (b d : B)
    → PreserveComp (prodComp (compEquality k (a ≡ c))
                             (compEquality k (b ≡ d)))
                   (compEquality k (t (a , b) ≡ t (c , d)))
                   (equalityCompHelper₂ a c b d t)
  eq (compPreserve (γ j k t a .a b .b) l m (refl , refl) (.refl , .refl) (.refl , .refl)) n ((refl , refl) , refl , refl) = equalityInvertibleMorphisms l n refl
  compPreserveCoin (γ j k t a c b d) l (w , x) (y , z) = γ k l (func (equalityCompHelper₂ a c b d t)) w y x z
ƛ (hCatEquality i S) {j} k refl = equalityInvertibleMorphisms j k refl
assoc (hCatEquality i S) {j} {k} refl refl refl refl = equalityInvertibleMorphisms j k refl
hcoin (hCatEquality i S) j x y = hCatEquality j (x ≡ y)
