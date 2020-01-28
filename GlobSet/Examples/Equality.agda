{-# OPTIONS --safe --without-K --sized-types #-}

module GlobSet.Examples.Equality where
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.Invertible
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
equalityCompHelper₂ f .f g .g F .func (refl , refl) = refl
equalityCompHelper₂ f f' g g' F .funcMorphisms j (α , β) (α' , β') =
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
equalityCompHelper i S j x y z .func (f , g) = trans f g
equalityCompHelper i S j x y z .funcMorphisms k (f , g) (f' , g') =
  equalityCompHelper₂ f f' g g' (func (equalityCompHelper i S j x y z))



compEquality : {a : Level} → (i : Size) → (S : Set a) → Composable i (equality i S)
compEquality i S .id j x = refl
compEquality i S .comp j x y z = equalityCompHelper i S j x y z
compEquality i S .compHigher j x y = compEquality j (x ≡ y)

equalityInvertibleMorphisms : {a : Level}
                            → (i : Size)
                            → {S : Set a}
                            → (j : Size< i)
                            → (x : S)
                            → InvertibleCell i (compEquality i S) j x x
equalityInvertibleMorphisms i S j .cell = refl
equalityInvertibleMorphisms i S j .invert .finv = refl
equalityInvertibleMorphisms i S j .invert .fR k = equalityInvertibleMorphisms S k refl
equalityInvertibleMorphisms i S j .invert .fL k = equalityInvertibleMorphisms S k refl

hCatEquality : {a : Level} → (i : Size) → (S : Set a) → HCat (equality i S) (compEquality i S)
hCatEquality i S .compPreserveId j x y z .idPreserve k l w = equalityInvertibleMorphisms k l refl
hCatEquality i S .compPreserveId j x y z .idPreserveCoin k (a , b) (c , d) =
  γ j k (λ v → trans (proj₁ v) (proj₂ v)) a c b d
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
  γ j k t a c b d .idPreserve l m w = equalityInvertibleMorphisms l m refl
  γ j k {S} t a c b d .idPreserveCoin l (e , f) (g , h) = γ k l (func (equalityCompHelper₂ a c b d t)) e g f h
hCatEquality i S .compPreserveComp j x y z .compPreserve k l (a , b) (.a , .b) (.a , .b) .eq m ((refl , refl) , (refl , refl)) = equalityInvertibleMorphisms k m refl
hCatEquality i S .compPreserveComp j x y z .compPreserveCoin k (a , b) (c , d) = γ j k (λ {(v₁ , v₂) → trans v₁ v₂}) a c b d
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
  γ j k t a .a b .b .compPreserve l m (refl , refl) (.refl , .refl) (.refl , .refl) .eq n ((refl , refl) , refl , refl) = equalityInvertibleMorphisms l n refl
  γ j k t a c b d .compPreserveCoin l (w , x) (y , z) = γ k l (func (equalityCompHelper₂ a c b d t)) w y x z
hCatEquality i S .ƛ {j} k refl = equalityInvertibleMorphisms j k refl
hCatEquality i S .ρ {j} k refl = equalityInvertibleMorphisms j k refl
hCatEquality i S .assoc {j} {k} refl refl refl = equalityInvertibleMorphisms j k refl
hCatEquality i S .hcoin j x y = hCatEquality j (x ≡ y)
