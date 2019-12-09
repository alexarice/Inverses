{-# OPTIONS --safe --without-K --sized-types #-}

module Minimal where
open import Agda.Builtin.Size
open import Data.Product

record GlobSet (i : Size) : Set₁ where
  coinductive
  field
    cells : Set
    morphisms : (j : Size< i) → cells → cells → GlobSet j

open GlobSet public

record GlobSetMorphism {i : Size} (G H : GlobSet i) : Set where
  coinductive
  field
    func : cells G → cells H
    funcMorphisms : (j : Size< i)
                  → (x y : cells G)
                  → GlobSetMorphism (morphisms G j x y)
                                    (morphisms H j (func x) (func y))

open GlobSetMorphism public

gComp : {i : Size} → {G H I : GlobSet i} → GlobSetMorphism H I → GlobSetMorphism G H → GlobSetMorphism G I
func (gComp ϕ ψ) x = func ϕ (func ψ x)
funcMorphisms (gComp ϕ ψ) j x y = gComp (funcMorphisms ϕ j (func ψ x) (func ψ y)) (funcMorphisms ψ j x y)


infixr 2 _×G_

_×G_ : ∀{i} → (G H : GlobSet i) → GlobSet i
cells (G ×G H) = cells G × cells H
morphisms (G ×G H) j (w , x) (y , z) = morphisms G j w y ×G morphisms H j x z

_×GM_ : {i : Size}
        {G H I J : GlobSet i}
      → GlobSetMorphism G H
      → GlobSetMorphism I J
      → GlobSetMorphism (G ×G I) (H ×G J)
func (ϕ ×GM ψ) (x , y) = (func ϕ x) , (func ψ y)
funcMorphisms (ϕ ×GM ψ) j (x , y) (x' , y') = (funcMorphisms ϕ j x x') ×GM funcMorphisms ψ j y y'

interchangeG : {i : Size}
             → (G H I J : GlobSet i)
             → GlobSetMorphism ((G ×G H) ×G (I ×G J)) ((G ×G I) ×G (H ×G J))
func (interchangeG G H I J) ((w , x) , (y , z)) = (w , y) , (x , z)
funcMorphisms (interchangeG G H I J) j ((w , x) , (y , z)) ((w' , x') , (y' , z')) =
  interchangeG (morphisms G j w w')
               (morphisms H j x x')
               (morphisms I j y y')
               (morphisms J j z z')



record Composable {i : Size} (G : GlobSet i) : Set where
  coinductive
  field
    id : (j : Size< i)
       → (x : cells G)
       → cells (morphisms G j x x)
    comp : (j : Size< i)
         → (x y z : cells G)
         → GlobSetMorphism (morphisms G j x y ×G morphisms G j y z)
                           (morphisms G j x z)
    compHigher : (j : Size< i)
               → (x y : cells G)
               → Composable (morphisms G j x y)

open Composable public

prodComp : {i : Size}
         → {A B : GlobSet i}
         → (ca : Composable A)
           (cb : Composable B)
         → Composable (A ×G B)
Composable.id (prodComp ca cb) j (x , y) = (id ca j x) , (id cb j y)
Composable.comp (prodComp {_} {A} {B} ca cb) j (x , x') (y , y') (z , z') = gComp ((comp ca j x y z) ×GM (comp cb j x' y' z')) (interchangeG (morphisms A j x y) (morphisms B j x' y') (morphisms A j y z) (morphisms B j y' z'))
Composable.compHigher (prodComp {_} {A} {B} ca cb) j (x , x') (y , y') = prodComp (compHigher ca j x y) (compHigher cb j x' y')

comp1 : {i : Size}
        {G : GlobSet i}
        (c : Composable G)
        {j : Size< i}
        {x y z : cells G}
      → cells (morphisms G j x y)
      → cells (morphisms G j y z)
      → cells (morphisms G j x z)
comp1 c {j} {x} {y} {z} f g = func (comp c j x y z) (f , g)

record BiInvertible {i : Size}
                    {G : GlobSet i}
                    (c : Composable G)
                    (j : Size< i)
                    {x y : cells G}
                    (f : cells (morphisms G j x y)) : Set₁ where
  coinductive
  field
    f* : cells (morphisms G j y x)
    *f : cells (morphisms G j y x)
    fR : (k : Size< j) → cells (morphisms (morphisms G j x x) k (comp1 c f f*) (id c j x))
    fL : (k : Size< j) → cells (morphisms (morphisms G j y y) k (comp1 c *f f) (id c j y))
    fRBiInv : (k : Size< j) → BiInvertible (compHigher c j x x) k (fR k)
    fLBiInv : (k : Size< j) → BiInvertible (compHigher c j y y) k (fL k)

open BiInvertible public

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

open HCat

idIsBiInv : {i : Size}
            (j : Size< i)
            {G : GlobSet i}
            (c : Composable G)
            (h : HCat G c)
          → (x : cells G)
          → BiInvertible c j (id c j x)
f* (idIsBiInv j c h x) = id c j x
*f (idIsBiInv j c h x) = id c j x
fR (idIsBiInv j c h x) k = ƛ h k (id c j x)
fL (idIsBiInv j c h x) k = ƛ h k (id c j x)
fRBiInv (idIsBiInv j c h x) k = ƛBiInv h k (id c j x)
fLBiInv (idIsBiInv j c h x) k = ƛBiInv h k (id c j x)

test : {i : Size}
     → (j : Size< i)
       {G : GlobSet i}
     → (c : Composable G)
     → (h : HCat G c)
     → (x y z : cells G)
     → (k : Size< j)
     → (f : cells (morphisms G j x y))
     → BiInvertible {j} (compHigher c j x y) k (id (compHigher c j x y) k f)
test {i} j {G} c h x y z k f = idIsBiInv k ? ? ?
-- (idIsBiInv {j} k {morphisms G j x y} (compHigher c j x y) (hcoin h j x y) f)
