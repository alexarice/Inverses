{-# OPTIONS --without-K  --sized-types --safe #-}

module GlobSet.Composition where
open import GlobSet
open import GlobSet.Product

record Composable {a : Level} (i : Size) (G : GlobSet a i) : Set a where
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
               → Composable j (morphisms G j x y)

open Composable public

prodComp : {a b : Level}
         → {i : Size}
         → {A : GlobSet a i}
         → {B : GlobSet b i}
         → (ca : Composable i A)
         → (cb : Composable i B)
         → Composable i (A ×G B)
Composable.id (prodComp ca cb) j (x , y) = (id ca j x) , (id cb j y)
Composable.comp (prodComp {A = A} {B = B} ca cb) j (x , x') (y , y') (z , z') =
  gComp ((comp ca j x y z) ×GM (comp cb j x' y' z'))
        (interchangeG (morphisms A j x y)
                      (morphisms B j x' y')
                      (morphisms A j y z)
                      (morphisms B j y' z'))
Composable.compHigher (prodComp {_} {A} {B} ca cb) j (x , x') (y , y') = prodComp (compHigher ca j x y) (compHigher cb j x' y')

comp1 : {a : Level}
        {i : Size}
        {G : GlobSet a i}
        (c : Composable i G)
        {j : Size< i}
        {x y z : cells G}
      → cells (morphisms G j x y)
      → cells (morphisms G j y z)
      → cells (morphisms G j x z)
comp1 c {j} {x} {y} {z} f g = func (comp c j x y z) (f , g)

comp2 : {a : Level}
        {i : Size}
        {G : GlobSet a i}
        (c : Composable i G)
        {j : Size< i}
        {k : Size< j}
        {x y z : cells G}
        {f f' : cells (morphisms G j x y)}
        {g g' : cells (morphisms G j y z)}
      → cells (morphisms (morphisms G j x y) k f f')
      → cells (morphisms (morphisms G j y z) k g g')
      → cells (morphisms (morphisms G j x z) k (comp1 {a} {i} c f g) (comp1 {a} {i} c f' g'))

comp2 c {j} {k} {x} {y} {z} {g} {g'} {f} {f'} α β =
  func (funcMorphisms (comp c j x y z)
                      k
                      (g , f)
                      (g' , f'))
       (α , β)
comp3 : {a : Level}
        {i : Size}
        {G : GlobSet a i}
        (c : Composable i G)
        {j : Size< i}
        {k : Size< j}
        {l : Size< k}
        {x y z : cells G}
        {f f' : cells (morphisms G j x y)}
        {g g' : cells (morphisms G j y z)}
      → {α α' : cells (morphisms (morphisms G j x y) k f f')}
      → {β β' : cells (morphisms (morphisms G j y z) k g g')}
      → cells (morphisms (morphisms (morphisms G j x y) k f f') l α α')
      → cells (morphisms (morphisms (morphisms G j y z) k g g') l β β')
      → cells (morphisms (morphisms (morphisms G j x z)
                                    k
                                    (comp1 {a} {i} c f g)
                                    (comp1 c f' g'))
                         l
                         (comp2 c α β)
                         (comp2 c α' β'))
comp3 c {j} {k} {l} {x} {y} {z} {g} {g'} {f} {f'} {α} {α'} {β} {β'} δ ε =
  func (funcMorphisms (funcMorphisms (comp c j x y z)
                                     k
                                     (g , f)
                                     (g' , f'))
                      l
                      (α , β)
                      (α' , β'))
       (δ , ε)
