{-# OPTIONS --without-K --safe --sized-types #-}

module GlobSet.HCat where

open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.Invertible.Core

record SameMorphism {a b : Level}
                    {i : Size}
                    {G : GlobSet a i}
                    {H : GlobSet b i}
                    (c : Composable i H)
                    (F₁ F₂ : GlobSetMorphism G H) : Set (suc (a ⊔ b)) where
  coinductive
  field
    eq : (j : Size< i)
       → (x : cells G)
       → InvertibleCell i c j (func F₁ x) (func F₂ x)

open SameMorphism public

record PreserveIden {a b : Level}
                    {i : Size}
                    {G : GlobSet a i}
                    {H : GlobSet b i}
                    (cg : Composable i G)
                    (ch  : Composable i H)
                    (F : GlobSetMorphism G H) : Set (suc (a ⊔ b)) where
  coinductive
  field
    idPreserve : (j : Size< i)
               → (k : Size< j)
               → (x : cells G)
               → InvertibleCell j
                                  (compHigher ch j (func F x) (func F x))
                                  k
                                  (func (funcMorphisms F j x x) (id cg j x))
                                  (id ch j (func F x))

    idPreserveCoin : (j : Size< i)
                   → (x y : cells G)
                   → PreserveIden (compHigher cg j x y)
                                  (compHigher ch j (func F x) (func F y))
                                  (funcMorphisms F j x y)

open PreserveIden public

record PreserveComp {a b : Level}
                    {i : Size}
                    {G : GlobSet a i}
                    {H : GlobSet b i}
                    (cg : Composable i G)
                    (ch : Composable i H)
                    (F : GlobSetMorphism G H) : Set (suc (a ⊔ b)) where
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

record HCat {a : Level} {i : Size} (G : GlobSet a i) (com : Composable i G) : Set (suc a) where
  coinductive
  field
    compPreserveId : (j : Size< i)
                   → (x y z : cells G)
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
      → InvertibleCell j
                       (compHigher com j x y)
                       k
                       (comp1 com (id com j x) f)
                       f
    ρ : {j : Size< i}
      → (k : Size< j)
      → {x y : cells G}
      → (f : cells (morphisms G j x y))
      → InvertibleCell j
                       (compHigher com j x y)
                       k
                       (comp1 com f (id com j y))
                       f
    assoc : {j : Size< i}
            {k : Size< j}
            {v x y z : cells G}
          → (a : cells (morphisms G j v x))
          → (b : cells (morphisms G j x y))
          → (c : cells (morphisms G j y z))
          → InvertibleCell j
                           (compHigher com j v z)
                           k
                           (comp1 com (comp1 com a b) c)
                           (comp1 com a (comp1 com b c))
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
               → InvertibleCell k
                                  (compHigher (compHigher com j x z)
                                              k
                                              (comp1 com a d)
                                              (comp1 com c f))
                                  l
                                  (comp1 (compHigher com j x z)
                                         (comp2 com α β)
                                         (comp2 com γ δ))
                                  (comp2 com
                                         (comp1 (compHigher com
                                                            j
                                                            x
                                                            y)
                                                α
                                                γ)
                                         (comp1 (compHigher com
                                                            j
                                                            y
                                                            z)
                                                β
                                                δ))

  interchange₁ {j} {k} {l} {x} {y} {z} {a} {b} {c} {d} {e} {f} α β γ δ =
    eq (compPreserve (compPreserveComp j x y z) k l (a , d) (b , e) (c , f)) l ((α , β) , γ , δ)

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
               → InvertibleCell l (compHigher (compHigher (compHigher com j x z)
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
                                           (comp1 (compHigher (compHigher com j y z) k c d) ψ ω))

  interchange₂ {j} {k} {l} {m} {x} {y} {z} {a} {b} {c} {d} {α} {β} {γ} {δ} {ε} {ζ} ϕ χ ψ ω =
    eq (compPreserve (compPreserveCoin (compPreserveComp j x y z) k (a , c) (b , d)) l m (α , δ) (β , ε) (γ , ζ)) m ((ϕ , ψ) , χ , ω)

  idenManip₁ : {j : Size< i}
               {k : Size< j}
               {l : Size< k}
               {x y z : cells G}
             → (f : cells (morphisms G j x y))
             → (g : cells (morphisms G j y z))
             → InvertibleCell k
                                (compHigher (compHigher com j x z)
                                            k
                                            (comp1 com f g)
                                            (comp1 com f g))
                                l
                                (comp2 com
                                       (id (compHigher com j x y) k f)
                                       (id (compHigher com j y z) k g))
                                       (id (compHigher com j x z) k (comp1 com f g))

  idenManip₁ {j} {k} {l} {x} {y} {z} f g = idPreserve (compPreserveId j x y z) k l (f , g)

  idenManip₂ : {j : Size< i}
               {k : Size< j}
               {l : Size< k}
               {m : Size< l}
               {x y z : cells G}
               {a b : cells (morphisms G j x y)}
               {c d : cells (morphisms G j y z)}
             → (α : cells (morphisms (morphisms G j x y) k a b))
             → (β : cells (morphisms (morphisms G j y z) k c d))
             → InvertibleCell l (compHigher (compHigher (compHigher com j x z)
                                                             k
                                                             (comp1 com a c)
                                                             (comp1 com b d))
                                                 l
                                                 (comp2 com α β)
                                                 (comp2 com α β))
                                     m
                                     (comp3 com
                                            (id (compHigher (compHigher com j x y)
                                                            k
                                                            a
                                                            b)
                                                l
                                                α)
                                            (id (compHigher (compHigher com j y z)
                                                            k
                                                            c
                                                            d)
                                                l
                                                β))
                                     (id (compHigher (compHigher com j x z)
                                                     k
                                                     (comp1 com a c)
                                                     (comp1 com b d))
                                         l
                                         (comp2 com α β))

  idenManip₂ {j} {k} {l} {m} {x} {y} {z} {a} {b} {c} {d} α β =
    idPreserve (idPreserveCoin (compPreserveId j x y z) k (a , c) (b , d)) l m (α , β)

open HCat public

record HigherCat {a : Level} (i : Size) (G : GlobSet a i) : Set (suc a) where
  field
    com : Composable i G
    hCat : HCat G com

open HigherCat public

coin : {a : Level}
     → {i : Size}
     → {G : GlobSet a i}
     → HigherCat i G
     → (j : Size< i)
     → (x y : cells G)
     → HigherCat j (morphisms G j x y)
coin h j x y .com = compHigher (com h) j x y
coin h j x y .hCat = hcoin (hCat h) j x y
