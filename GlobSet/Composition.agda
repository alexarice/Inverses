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

descComp : {i : Size}
           {G : GlobSet i}
           ⦃ _ : Composable G ⦄
           {j : Size}
         → (d : Descendant G j)
         → Composable (realise d)
descComp ⦃ c ⦄ Orig = c
descComp {j = j} (Child d k x y) = Composable.compHigher (descComp d) j x y


prodComp : {i : Size}
         → (A B : GlobSet i)
           {{_ : Composable A}}
           {{_ : Composable B}}
         → Composable (A ×G B)
Composable.id (prodComp A B) j (x , y) = (id j x) , (id j y)
Composable.comp (prodComp A B) j (x , x') (y , y') (z , z') = gComp ((comp j x y z) ×GM (comp j x' y' z')) (interchangeG (morphisms A j x y) (morphisms B j x' y') (morphisms A j y z) (morphisms B j y' z'))
Composable.compHigher (prodComp A B) j (x , x') (y , y') = prodComp (morphisms A j x y) (morphisms B j x' y') ⦃ compHigher j x y ⦄ ⦃ compHigher j x' y' ⦄

descExComp : {i : Size}
             {G : GlobSet i}
             ⦃ _ : Composable G ⦄
             {j : Size}
           → (d : ExDescendant G j)
           → Composable (realiseEx d)
descExComp ⦃ c ⦄ OrigEx = c
descExComp {j = j} (ChildEx d k x y) = Composable.compHigher (descExComp d) j x y
descExComp (Prod d₁ d₂) = prodComp (realiseEx d₁) (realiseEx d₂) ⦃ descExComp d₁ ⦄ ⦃ descExComp d₂ ⦄

idd : {h : Size}
      {G : GlobSet h}
      ⦃ _ : Composable G ⦄
      {i : Size}
    → (d : Descendant G i)
    → (j : Size< i)
    → (x : cells (realise d))
    → cells (morphisms (realise d) j x x)
idd d j x = Composable.id (descComp d) j x

compd : {h : Size}
        {G : GlobSet h}
        ⦃ _ : Composable G ⦄
        {i : Size}
      → (d : Descendant G i)
      → (j : Size< i)
      → (x y z : cells (realise d))
      → GlobSetMorphism (morphisms (realise d) j x y ×G morphisms (realise d) j y z)
                        (morphisms (realise d) j x z)
compd d j x y z = Composable.comp (descComp d) j x y z

idde : {h : Size}
      {G : GlobSet h}
      ⦃ _ : Composable G ⦄
      {i : Size}
    → (d : ExDescendant G i)
    → (j : Size< i)
    → (x : cells (realiseEx d))
    → cells (morphisms (realiseEx d) j x x)
idde d j x = Composable.id (descExComp d) j x

compde : {h : Size}
        {G : GlobSet h}
        ⦃ _ : Composable G ⦄
        {i : Size}
      → (d : ExDescendant G i)
      → (j : Size< i)
      → (x y z : cells (realiseEx d))
      → GlobSetMorphism (morphisms (realiseEx d) j x y ×G morphisms (realiseEx d) j y z)
                        (morphisms (realiseEx d) j x z)
compde d j x y z = Composable.comp (descExComp d) j x y z

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
comp1 d {j} {x} {y} {z} f g = func (compd d j x y z) (f , g)
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
  func (funcMorphisms (compd d j x y z)
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
  func (funcMorphisms (funcMorphisms (compd d j x y z)
                                     k
                                     (g , f)
                                     (g' , f'))
                      l
                      (α , β)
                      (α' , β'))
       (δ , ε)
