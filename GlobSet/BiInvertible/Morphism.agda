{-# OPTIONS --without-K --sized-types --safe #-}

module GlobSet.BiInvertible.Morphism where

open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible

record BiInvertibleMorphism {a : Level}
                            {i : Size}
                            {G : GlobSet a i}
                            {c : Composable i G}
                            {x y : cells G}
                            {j : Size< i}
                            {f : cells (morphisms G j x y)}
                            (bf₁ bf₂ : BiInvertible i c j f) : Set (suc a) where
  coinductive
  field
    leftMorphism : (k : Size< j) → cells (morphisms (morphisms G j y x) k (*f bf₁) (*f bf₂))
    rightMorphism : (k : Size< j) → cells (morphisms (morphisms G j y x) k (f* bf₁) (f* bf₂))
    leftEquiv : (k : Size< j)
              → (l : Size< k)
              → cells (morphisms (morphisms (morphisms G j y y)
                                            k
                                            (comp1 c (*f bf₁) f)
                                            (id c j y))
                                 l
                                 (comp1 (compHigher c j y y)
                                        (comp2 c
                                               (leftMorphism k)
                                               (id (compHigher c j x y) k f))
                                        (fL bf₂ k))
                                 (fL bf₁ k))
    rightEquiv : (k : Size< j)
               → (l : Size< k)
               → cells (morphisms (morphisms (morphisms G j x x)
                                             k
                                             (comp1 c f (f* bf₁))
                                             (id c j x))
                                  l
                                  (comp1 (compHigher c j x x)
                                         (comp2 c
                                                (id (compHigher c j x y) k f)
                                                (rightMorphism k))
                                         (fR bf₂ k))
                                  (fR bf₁ k))
    leftEquivBiInv : (k : Size< j)
                   → (l : Size< k)
                   → BiInvertible k (compHigher (compHigher c j y y) k (comp1 c (*f bf₁) f) (id c j y) ) l (leftEquiv k l)

    rightEquivBiInv : (k : Size< j)
                    → (l : Size< k)
                    → BiInvertible k (compHigher (compHigher c j x x) k (comp1 c f (f* bf₁)) (id c j x)) l (rightEquiv k l)
