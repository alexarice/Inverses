{-# OPTIONS --without-K #-}

module GlobSet.HCat where

open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible
open import GlobSet.Descendant

record SameMorphism {h i : Size}
                    {G : GlobSet i}
                    {H : GlobSet h}
                    ⦃ _ : Composable H ⦄
                    (d : Descendant H i)
                    (F₁ F₂ : GlobSetMorphism G (realise d)) : Set₁ where
  coinductive
  field
    eq : (j : Size< i)
       → (x : cells G)
       → cells (morphisms (realise d) j (func F₁ x) (func F₂ x))
    eqBiInv : (j : Size< i) → (x : cells G) → BiInvertible j (realise d) {{descComp d}} (eq j x)

open SameMorphism public

record PreserveIden {i : Size}
                    {G H : GlobSet i}
                    ⦃ _ : Composable G ⦄
                    ⦃ _ : Composable H ⦄
                    (F : GlobSetMorphism G H) : Set₁ where
  coinductive
  field
    idPreserve : (j : Size< i)
               → (k : Size< j)
               → (x : cells G)
               → cells (morphisms (morphisms H j (func F x) (func F x))
                       k
                       (func (funcMorphisms F j x x) (id j x)) (id j (func F x)))
    idPreserveBiInv : (j : Size< i)
                    → (k : Size< j)
                    → (x : cells G)
                    → BiInvertible k
                                   (morphisms H j (func F x) (func F x))
                                   ⦃ compHigher j (func F x) (func F x) ⦄
                                   (idPreserve j k x)
    idPreserveCoin : (j : Size< i)
                   → (x y : cells G)
                   → PreserveIden ⦃ compHigher j x y ⦄
                                  ⦃ compHigher j (func F x) (func F y) ⦄
                                  (funcMorphisms F j x y)

open PreserveIden public

record PreserveComp {h i : Size}
                    {G H : GlobSet h}
                    ⦃ _ : Composable G ⦄
                    ⦃ _ : Composable H ⦄
                    (d₁ : Descendant G i)
                    (d₂ : Descendant H i)
                    (F : GlobSetMorphism (realise d₁) (realise d₂)) : Set₁ where
  coinductive
  field
    compPreserve : (j : Size< i)
                 → (k : Size< j)
                 → (x y z : cells (realise d₁))
                 → SameMorphism (Child d₂ j (func F x) (func F z))
                                (gComp (comp {{descComp d₂}} j (func F x) (func F y) (func F z))
                                       (funcMorphisms F j y z ×GM funcMorphisms F j x y))
                                (gComp (funcMorphisms F j x z) (comp {{descComp d₁}} j x y z))
    compPreserveCoin : (j : Size< i)
                     → (x y : cells (realise d₁))
                     → PreserveComp (Child d₁ j x y)
                                    (Child d₂ j (func F x) (func F y))
                                    (funcMorphisms F j x y)

open PreserveComp public

record HCat {i : Size} (G : GlobSet i) ⦃ _ : Composable G ⦄ : Set₁ where
  coinductive
  field
    compPreserveId : (j : Size< i)
                   → {x y z : cells G}
                   → PreserveIden ⦃ prodComp (morphisms G j y z)
                                             (morphisms G j x y)
                                             ⦃ compHigher j y z ⦄
                                             ⦃ compHigher j x y ⦄ ⦄
                                  ⦃ compHigher j x z ⦄
                                  (comp j x y z)
    ƛ : {j : Size< i}
      → (k : Size< j)
      → {x y : cells G}
      → (f : cells (morphisms G j x y))
      → cells (morphisms (morphisms G j x y) k (comp1 Orig (id j y) f) f)
    ƛBiInv : {j : Size< i}
           → (k : Size< j)
           → {x y : cells G}
           → (f : cells (morphisms G j x y))
           → BiInvertible k (morphisms G j x y) ⦃ compHigher j x y ⦄ (ƛ k f)
    compPreserveComp : (j : Size< i)
                     → (x y z : cells G)
                     → PreserveComp (Prod (Child Orig j y z)
                                          (Child Orig j x y))
                                    (Child Orig j x z)
                                    (comp j x y z)
    hcoin : (j : Size< i)
          → (x y : cells G)
          → HCat (morphisms G j x y) ⦃ compHigher j x y ⦄
  interchange₁ : {j : Size< i}
                 {k : Size< j}
                 {l : Size< k}
                 {x y z : cells G}
                 {a b c : cells (morphisms G j x y)}
                 {d e f : cells (morphisms G j y z)}
               → (α : cells (morphisms (morphisms G j x y) k a b))
               → (β : cells (morphisms (morphisms G j y z) k d e))
               → (γ : cells (morphisms (morphisms G j x y) k b c))
               → (δ : cells (morphisms (morphisms G j y z) k e f))
               → cells (morphisms (morphisms (morphisms G j x z) k (comp1 Orig d a) (comp1 Orig f c))
                       l
                       (comp1 (Child Orig j x z)
                              (comp2 Orig δ γ)
                              (comp2 Orig β α))
                       (comp2 Orig
                              (comp1 (Child Orig j y z)
                                     δ
                                     β)
                              (comp1 (Child Orig j x y)
                                     γ
                                     α)))
  interchange₁ {j} {k} {l} {x} {y} {z} {a} {b} {c} {d} {e} {f} α β γ δ =
    eq (compPreserve (compPreserveComp j x y z)
                     k
                     l
                     (d , a)
                     (e , b)
                     (f , c))
       l
       ((δ , γ) , (β , α))

open HCat ⦃ ... ⦄ public
