{-# OPTIONS --without-K --sized-types #-}

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
    eqBiInv : (j : Size< i) → (x : cells G) → BiInvertible j d (eq j x)

open SameMorphism public

record PreserveIden {h i : Size}
                    {G H : GlobSet h}
                    ⦃ _ : Composable G ⦄
                    ⦃ _ : Composable H ⦄
                    (d₁ : ExDescendant G i)
                    (d₂ : ExDescendant H i)
                    (F : GlobSetMorphism (realiseEx d₁) (realiseEx d₂)) : Set₁ where
  coinductive
  field
    idPreserve : (j : Size< i)
               → (k : Size< j)
               → (x : cells (realiseEx d₁))
               → cells (morphisms (morphisms (realiseEx d₂) j (func F x) (func F x))
                       k
                       (func (funcMorphisms F j x x) (idde d₁ j x)) (idde d₂ j (func F x)))
    idPreserveBiInv : (j : Size< i)
                    → (k : Size< j)
                    → (x : cells (realiseEx d₁))
                    → BiInvertible k (ChildEx d₂ j (func F x) (func F x))
                                   (idPreserve j k x)
    idPreserveCoin : (j : Size< i)
                   → (x y : cells (realise d₁))
                   → PreserveIden (Child d₁ j x y)
                                  (Child d₂ j (func F x) (func F y))
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
                                       (funcMorphisms F j x y ×GM funcMorphisms F j y z))
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
                   → (x y z : cells G)
                   → PreserveIden (Prod (Child Orig j x y) (Child Orig j y z))
                                  (Child Orig j x z)
                                  (comp j x y z)
    compPreserveComp : (j : Size< i)
                     → (x y z : cells G)
                     → PreserveComp (Prod (Child Orig j x y)
                                          (Child Orig j y z))
                                    (Child Orig j x z)
                                    (comp j x y z)
    ƛ : {j : Size< i}
      → (k : Size< j)
      → {x y : cells G}
      → (f : cells (morphisms G j x y))
      → cells (morphisms (morphisms G j x y) k (comp1 Orig (id j x) f) f)
    ƛBiInv : {j : Size< i}
           → (k : Size< j)
           → {x y : cells G}
           → (f : cells (morphisms G j x y))
           → BiInvertible k (Child Orig j x y) (ƛ k f)
    assoc : {j : Size< i}
            {k : Size< j}
            {u v x y z : cells G}
          → (a : cells (morphisms G j u v))
          → (b : cells (morphisms G j v x))
          → (c : cells (morphisms G j x y))
          → (d : cells (morphisms G j y z))
          → cells (morphisms (morphisms G j u z)
                             k
                             (comp1 Orig
                                    (comp1 Orig a b)
                                    (comp1 Orig c d))
                             (comp1 Orig
                                    a (comp1 Orig
                                             (comp1 Orig b c)
                                             d)))
    assocBiInv : {j : Size< i}
                 {k : Size< j}
                 {u v x y z : cells G}
               → (a : cells (morphisms G j u v))
               → (b : cells (morphisms G j v x))
               → (c : cells (morphisms G j x y))
               → (d : cells (morphisms G j y z))
               → BiInvertible k (Child Orig j u z) (assoc a b c d)
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
               → cells (morphisms (morphisms (morphisms G j x z)
                                             k
                                             (comp1 Orig a d)
                                             (comp1 Orig c f))
                       l
                       (comp1 (Child Orig j x z)
                              (comp2 Orig α β)
                              (comp2 Orig γ δ))
                       (comp2 Orig
                              (comp1 (Child Orig j x y)
                                     α
                                     γ)
                              (comp1 (Child Orig j y z)
                                     β
                                     δ)))

  interchange₁ {j} {k} {l} {x} {y} {z} {a} {b} {c} {d} {e} {f} α β γ δ =
    eq (compPreserve (compPreserveComp j x y z)
                     k
                     l
                     (a , d) (b , e) (c , f))
       l
       ((α , β) , γ , δ)
  interchange₂ : {j : Size< i}
                 {k : Size< j}
                 {l : Size< k}
                 {m : Size< l}
                 {x y z : cells G}
                 {a b : cells (morphisms G j x y)}
                 {c d : cells (morphisms G j y z)}
                 {α β γ : cells (morphisms (morphisms G j x y) k a b)}
                 {δ ε ζ : cells (morphisms (morphisms G j y z) k c d)}
               → (ϕ : cells (morphisms (morphisms (morphisms G j x y) k a b) l α β))
               → (χ : cells (morphisms (morphisms (morphisms G j x y) k a b) l β γ))
               → (ψ : cells (morphisms (morphisms (morphisms G j y z) k c d) l δ ε))
               → (ω : cells (morphisms (morphisms (morphisms G j y z) k c d) l ε ζ))
               → cells (morphisms (morphisms (morphisms (morphisms G j x z)
                                                        k
                                                        (comp1 Orig a c)
                                                        (comp1 Orig b d))
                                             l
                                             (comp2 Orig α δ)
                                             (comp2 Orig γ ζ))
                                  m
                                  (comp1 (Child (Child Orig j x z)
                                                k
                                                (comp1 Orig a c)
                                                (comp1 Orig b d))
                                         (comp3 Orig ϕ ψ)
                                         (comp3 Orig χ ω))
                                  (comp3 Orig
                                         (comp1 (Child (Child Orig j x y) k a b) ϕ χ)
                                         (comp1 (Child (Child Orig j y z) k c d) ψ ω)))

  interchange₂ {j} {k} {l} {m} {x} {y} {z} {a} {b} {c} {d} {α} {β} {γ} {δ} {ε} {ζ} ϕ χ ψ ω =
    eq (compPreserve (compPreserveCoin (compPreserveComp j x y z)
                                       k
                                       (a , c)
                                       (b , d))
                     l
                     m
                     (α , δ)
                     (β , ε)
                     (γ , ζ))
       m
       ((ϕ , ψ) , χ , ω)



  idenManip₂ : {j : Size< i}
               {k : Size< j}
               {l : Size< k}
               {m : Size< l}
               {x y z : cells G}
               {a b : cells (morphisms G j x y)}
               {c d : cells (morphisms G j y z)}
             → (α : cells (morphisms (morphisms G j x y) k a b))
             → (β : cells (morphisms (morphisms G j y z) k c d))
             → cells (morphisms (morphisms (morphisms (morphisms G j x z)
                                                      k
                                                      (comp1 Orig a c)
                                                      (comp1 Orig b d))
                                           l
                                           (comp2 Orig α β)
                                           (comp2 Orig α β))
                                m
                                (comp3 Orig
                                       (idd (Child (Child Orig j x y) k a b) l α)
                                       (idd (Child (Child Orig j y z) k c d) l β))
                                (idd (Child (Child Orig j x z)
                                            k
                                            (comp1 Orig a c)
                                            (comp1 Orig b d))
                                     l
                                     (comp2 Orig α β)))
  idenManip₂ {j} {k} {l} {m} {x} {y} {z} {a} {b} {c} {d} α β =
    idPreserve (idPreserveCoin (compPreserveId j x y z) k (a , c) (b , d)) l m (α , β)




open HCat ⦃ ... ⦄ public

descHCat : {h : Size}
           {G : GlobSet h}
           ⦃ _ : Composable G ⦄
           ⦃ _ : HCat G ⦄
           {i : Size}
         → (d : Descendant G i)
         → HCat (realise d) ⦃ descComp d ⦄
descHCat ⦃ _ ⦄ ⦃ hcat ⦄ Orig = hcat
descHCat {i = i} (Child d k x y) = HCat.hcoin ⦃ descComp d ⦄ (descHCat d) i x y

compPreserveIdD : {h : Size}
                  {G : GlobSet h}
                  ⦃ _ : Composable G ⦄
                  {i : Size}
                → (des : Descendant G i)
                → (j : Size< i)
                → (x y z : cells (realise des))
                → PreserveIden (Prod (Child des j x y) (Child des j y z))
                                  (Child des j x z)
                                  (compd des j x y z)
compPreserveIdD des j x y z = {!!} -- HCat.compPreserveId (descHCat) ? ? ? ?

idenManip₁ : {h : Size}
             {G : GlobSet h}
             ⦃ _ : Composable G ⦄
             {i : Size}
             (des : Descendant G i)
             {j : Size< i}
             {k : Size< j}
             {l : Size< k}
             {x y z : cells (realise des)}
           → (f : cells (morphisms (realise des) j x y))
           → (g : cells (morphisms (realise des) j y z))
           → cells (morphisms (morphisms (morphisms (realise des) j x z)
                                           k
                                           (comp1 des f g)
                                           (comp1 des f g))
                                l
                                (comp2 des
                                       (idd (Child des j x y) k f)
                                       (idd (Child des j y z) k g))
                                (idd (Child des j x z) k (comp1 des f g)))
idenManip₁ des {j} {k} {l} {x} {y} {z} f g = idPreserve (compPreserveIdD des j x y z) k l (f , g)
