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

open Composable {{...}} public

prodComp : {i : Size}
         → (A B : GlobSet i)
           {{_ : Composable A}}
           {{_ : Composable B}}
         → Composable (A ×G B)
Composable.id (prodComp A B) j (x , y) = (id j x) , (id j y)
Composable.comp (prodComp A B) j (x , x') (y , y') (z , z') = gComp ((comp j x y z) ×GM (comp j x' y' z')) (interchangeG (morphisms A j x y) (morphisms B j x' y') (morphisms A j y z) (morphisms B j y' z'))
Composable.compHigher (prodComp A B) j (x , x') (y , y') = prodComp (morphisms A j x y) (morphisms B j x' y') ⦃ compHigher j x y ⦄ ⦃ compHigher j x' y' ⦄

descComp : {i : Size}
           {G : GlobSet i}
           ⦃ _ : Composable G ⦄
           {j : Size}
         → (d : Descendant G j)
         → Composable (realise d)
descComp ⦃ c ⦄ Orig = c
descComp {j = j} (Child d k x y) = Composable.compHigher (descComp d) j x y
descComp (Prod d₁ d₂) = prodComp (realise d₁) (realise d₂) ⦃ descComp d₁ ⦄ ⦃ descComp d₂ ⦄

idd : {h : Size}
      {G : GlobSet h}
      ⦃ _ : Composable G ⦄
      {i : Size}
    → (d : Descendant G i)
    → (j : Size< i)
    → (x : cells (realise d))
    → cells (morphisms (realise d) j x x)
idd d j x = Composable.id (descComp d) j x

comp1 : {h : Size}
        {G : GlobSet h}
        ⦃ _ : Composable G ⦄
        {i : Size}
        (d : Descendant G i)
        {j : Size< i}
        {x y z : cells (realise d)}
      → cells (morphisms (realise d) j x y)
      → cells (morphisms (realise d) j y z)
      → cells (morphisms (realise d) j x z)
comp1 d {j} {x} {y} {z} f g = func (Composable.comp (descComp d) j x y z) (f , g)
comp2 : {h : Size}
        {G : GlobSet h}
        ⦃ _ : Composable G ⦄
        {i : Size}
        (d : Descendant G i)
        {j : Size< i}
        {k : Size< j}
        {x y z : cells (realise d)}
        {f f' : cells (morphisms (realise d) j x y)}
        {g g' : cells (morphisms (realise d) j y z)}
      → cells (morphisms (morphisms (realise d) j x y) k f f')
      → cells (morphisms (morphisms (realise d) j y z) k g g')
        → cells (morphisms (morphisms (realise d) j x z) k (comp1 d f g) (comp1 d f' g'))
comp2 d {j} {k} {x} {y} {z} {g} {g'} {f} {f'} α β =
  func (funcMorphisms (Composable.comp (descComp d) j x y z)
                      k
                      (g , f)
                      (g' , f'))
       (α , β)
comp3 : {h : Size}
        {G : GlobSet h}
        ⦃ _ : Composable G ⦄
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
                                    (comp1 d f g)
                                    (comp1 d f' g'))
                         l
                         (comp2 d α β)
                         (comp2 d α' β'))
comp3 d {j} {k} {l} {x} {y} {z} {g} {g'} {f} {f'} {α} {α'} {β} {β'} δ ε =
  func (funcMorphisms (funcMorphisms (Composable.comp (descComp d) j x y z)
                                     k
                                     (g , f)
                                     (g' , f'))
                      l
                      (α , β)
                      (α' , β'))
       (δ , ε)
