{-# OPTIONS --without-K #-}

module GlobSet.HCat where

open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible

record SameMorphism {i : Size}
                    {G : GlobSet i}
                    {H : GlobSet i}
                    (c : Composable H)
                    (F₁ F₂ : GlobSetMorphism G H) : Set₁ where
  coinductive
  field
    eq : (j : Size< i)
       → (x : cells G)
       → cells (morphisms H j (func F₁ x) (func F₂ x))
    eqBiInv : (j : Size< i) → (x : cells G) → BiInvertible c j (eq j x)

open SameMorphism public

record PreserveIden {i : Size}
                    {G H : GlobSet i}
                    (cg : Composable G)
                    (ch  : Composable H)
                    (F : GlobSetMorphism G H) : Set₁ where
  coinductive
  field
    idPreserve : (j : Size< i)
               → (k : Size< j)
               → (x : cells G)
               → cells (morphisms (morphisms H j (func F x) (func F x))
                       k
                       (func (funcMorphisms F j x x) (id cg j x)) (id ch j (func F x)))
    idPreserveBiInv : (j : Size< i)
                    → (k : Size< j)
                    → (x : cells G)
                    → BiInvertible (compHigher ch j (func F x) (func F x))
                                   k
                                   (idPreserve j k x)
    idPreserveCoin : (j : Size< i)
                   → (x y : cells G)
                   → PreserveIden (compHigher cg j x y)
                                  (compHigher ch j (func F x) (func F y))
                                  (funcMorphisms F j x y)

open PreserveIden public

record PreserveComp {i : Size}
                    {G H : GlobSet i}
                    (cg : Composable G)
                    (ch : Composable H)
                    (F : GlobSetMorphism G H) : Set₁ where
  coinductive
  field
    compPreserve : (j : Size< i)
                 → (k : Size< j)
                 → (x y z : cells G)
                 → SameMorphism (compHigher ch j (func F x) (func F z))
                                (gComp (comp ch j (func F x) (func F y) (func F z))
                                       (funcMorphisms F j x y ×GM funcMorphisms F j y z))
                                (gComp (funcMorphisms F j x z) (comp cg j x y z))
    compPreserveCoin : (j : Size< i)
                     → (x y : cells G)
                     → PreserveComp (compHigher cg j x y)
                                    (compHigher ch j (func F x) (func F y))
                                    (funcMorphisms F j x y)

open PreserveComp public

record HCat {i : Size} (G : GlobSet i) (com : Composable G) : Set₁ where
  coinductive
  field
    compPreserveId : (j : Size< i)
                   → {x y z : cells G}
                   → PreserveIden (prodComp (compHigher com j x y) (compHigher com j y z))
                                  (compHigher com j x z)
                                  (comp com j x y z)
    compPreserveComp : (j : Size< i)
                     → (x y z : cells G)
                     → PreserveComp (prodComp (compHigher com j x y) (compHigher com j y z))
                                    (compHigher com j x z)
                                    (comp com j x y z)
    ƛ : {j : Size< i}
      → (k : Size< j)
      → {x y : cells G}
      → (f : cells (morphisms G j x y))
      → cells (morphisms (morphisms G j x y) k (comp1 com (id com j x) f) f)
    ƛBiInv : {j : Size< i}
           → (k : Size< j)
           → {x y : cells G}
           → (f : cells (morphisms G j x y))
           → BiInvertible (compHigher com j x y) k (ƛ k f)
    assoc : {j : Size< i}
            {k : Size< j}
            {u v x y z : cells G}
          → (a : cells (morphisms G j u v))
          → (b : cells (morphisms G j v x))
          → (c : cells (morphisms G j x y))
          → (d : cells (morphisms G j y z))
          → cells (morphisms (morphisms G j u z)
                             k
                             (comp1 com
                                    (comp1 com a b)
                                    (comp1 com c d))
                             (comp1 com
                                    a (comp1 com
                                             (comp1 com b c)
                                             d)))
    assocBiInv : {j : Size< i}
                 {k : Size< j}
                 {u v x y z : cells G}
               → (a : cells (morphisms G j u v))
               → (b : cells (morphisms G j v x))
               → (c : cells (morphisms G j x y))
               → (d : cells (morphisms G j y z))
               → BiInvertible (compHigher com j u z) k (assoc a b c d)
    hcoin : (j : Size< i)
          → (x y : cells G)
          → HCat (morphisms G j x y) (compHigher com j x y)
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
                                             (comp1 com a d)
                                             (comp1 com c f))
                       l
                       (comp1 (compHigher com j x z)
                              (comp2 com α β)
                              (comp2 com γ δ))
                       (comp2 com
                              (comp1 (compHigher com j x y)
                                     α
                                     γ)
                              (comp1 (compHigher com j y z)
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
                                                        (comp1 com a c)
                                                        (comp1 com b d))
                                             l
                                             (comp2 com α δ)
                                             (comp2 com γ ζ))
                                  m
                                  (comp1 (compHigher (compHigher com j x z)
                                                     k
                                                     (comp1 com a c)
                                                     (comp1 com b d))
                                         (comp3 com ϕ ψ)
                                         (comp3 com χ ω))
                                  (comp3 com
                                         (comp1 (compHigher (compHigher com j x y) k a b) ϕ χ)
                                         (comp1 (compHigher (compHigher com j y z) k c d) ψ ω)))

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

  idenManip₁ : {j : Size< i}
               {k : Size< j}
               {l : Size< k}
               {x y z : cells G}
             → (f : cells (morphisms G j x y))
             → (g : cells (morphisms G j y z))
             → cells (morphisms (morphisms (morphisms G j x z)
                                           k
                                           (comp1 com f g)
                                           (comp1 com f g))
                                l
                                (comp2 com
                                       (id (compHigher com j x y) k f)
                                       (id (compHigher com j y z) k g))
                                (id (compHigher com j x z) k (comp1 com f g)))
  idenManip₁ {j} {k} {l} {x} {y} {z} f g = idPreserve (compPreserveId j) k l (f , g)

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
                                                      (comp1 com a c)
                                                      (comp1 com b d))
                                           l
                                           (comp2 com α β)
                                           (comp2 com α β))
                                m
                                (comp3 com
                                       (id (compHigher (compHigher com j x y) k a b) l α)
                                       (id (compHigher (compHigher com j y z) k c d) l β))
                                (id (compHigher (compHigher com j x z) k (comp1 com a c) (comp1 com b d))
                                    l
                                    (comp2 com α β)))
  idenManip₂ {j} {k} {l} {m} {x} {y} {z} {a} {b} {c} {d} α β =
    idPreserve (idPreserveCoin (compPreserveId j) k (a , c) (b , d)) l m (α , β)


open HCat public
