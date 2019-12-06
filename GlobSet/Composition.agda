{-# OPTIONS --without-K  --sized-types --allow-unsolved-metas #-}

module GlobSet.Composition where
open import GlobSet
open import GlobSet.Product
open import GlobSet.Descendant

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
         → (A B : GlobSet i)
         → (ca : Composable A)
           (cb : Composable B)
         → Composable (A ×G B)
Composable.id (prodComp A B ca cb) j (x , y) = (id ca j x) , (id cb j y)
Composable.comp (prodComp A B ca cb) j (x , x') (y , y') (z , z') = gComp ((comp ca j x y z) ×GM (comp cb j x' y' z')) (interchangeG (morphisms A j x y) (morphisms B j x' y') (morphisms A j y z) (morphisms B j y' z'))
Composable.compHigher (prodComp A B ca cb) j (x , x') (y , y') = prodComp (morphisms A j x y) (morphisms B j x' y') (compHigher ca j x y) (compHigher cb j x' y')

descComp : {i : Size}
           {G : GlobSet i}
         → (c : Composable G)
           {j : Size}
         → (d : Descendant G j)
         → Composable (realise d)
descComp c Orig = c
descComp c {j = j} (Child d k x y) = Composable.compHigher (descComp c d) j x y
descComp c (Prod d₁ d₂) = prodComp (realise d₁) (realise d₂) (descComp c d₁) (descComp c d₂)

idd : {h : Size}
      {G : GlobSet h}
    → (c  : Composable G)
      {i : Size}
    → (d : Descendant G i)
    → (j : Size< i)
    → (x : cells (realise d))
    → cells (morphisms (realise d) j x x)
idd c d j x = Composable.id (descComp c d) j x

compd : {h : Size}
        {G : GlobSet h}
        (c : Composable G)
        {i : Size}
      → (d : Descendant G i)
      → (j : Size< i)
      → (x y z : cells (realise d))
      → GlobSetMorphism (morphisms (realise d) j x y ×G morphisms (realise d) j y z)
                        (morphisms (realise d) j x z)
compd c d j x y z = Composable.comp (descComp c d) j x y z

comp1 : {h : Size}
        {G : GlobSet h}
        (c : Composable G)
        {i : Size}
        (d : Descendant G i)
        {j : Size< i}
        {x y z : cells (realise d)}
      → cells (morphisms (realise d) j x y)
      → cells (morphisms (realise d) j y z)
      → cells (morphisms (realise d) j x z)
comp1 c d {j} {x} {y} {z} f g = func (compd c d j x y z) (f , g)

comp2 : {h : Size}
        {G : GlobSet h}
        (c : Composable G)
        {i : Size}
        (d : Descendant G i)
        {j : Size< i}
        {k : Size< j}
        {x y z : cells (realise d)}
        {f f' : cells (morphisms (realise d) j x y)}
        {g g' : cells (morphisms (realise d) j y z)}
      → cells (morphisms (morphisms (realise d) j x y) k f f')
      → cells (morphisms (morphisms (realise d) j y z) k g g')
        → cells (morphisms (morphisms (realise d) j x z) k (comp1 c d f g) (comp1 c d f' g'))
comp2 c d {j} {k} {x} {y} {z} {g} {g'} {f} {f'} α β =
  func (funcMorphisms (compd c d j x y z)
                      k
                      (g , f)
                      (g' , f'))
       (α , β)
comp3 : {h : Size}
        {G : GlobSet h}
        (c : Composable G)
        {i : Size}
        (d : Descendant G i)
        {j : Size< i}
        {k : Size< j}
        {l : Size< k}
        {x y z : cells (realise d)}
        {f f' : cells (morphisms (realise d) j x y)}
        {g g' : cells (morphisms (realise d) j y z)}
      → {α α' : cells (morphisms (morphisms (realise d) j x y) k f f')}
      → {β β' : cells (morphisms (morphisms (realise d) j y z) k g g')}
      → cells (morphisms (morphisms (morphisms (realise d) j x y) k f f') l α α')
      → cells (morphisms (morphisms (morphisms (realise d) j y z) k g g') l β β')
      → cells (morphisms (morphisms (morphisms (realise d) j x z)
                                    k
                                    (comp1 c d f g)
                                    (comp1 c d f' g'))
                         l
                         (comp2 c d α β)
                         (comp2 c d α' β'))
comp3 c d {j} {k} {l} {x} {y} {z} {g} {g'} {f} {f'} {α} {α'} {β} {β'} δ ε =
  func (funcMorphisms (funcMorphisms (compd c d j x y z)
                                     k
                                     (g , f)
                                     (g' , f'))
                      l
                      (α , β)
                      (α' , β'))
       (δ , ε)
