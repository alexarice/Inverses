{-# OPTIONS --without-K --sized-types --safe #-}

module GlobSet.BiInvertible where
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible.Core public
open import GlobSet.HCat


idIsBiInv : {a : Level}
            {i : Size}
            (j : Size< i)
            {G : GlobSet a i}
            (c : Composable i G)
            (h : HCat G c)
          → (x : cells G)
          → BiInvertible i c j (id c j x)
f* (idIsBiInv j c h x) = id c j x
*f (idIsBiInv j c h x) = id c j x
fR (idIsBiInv j c h x) k = ƛ h k (id c j x)
fL (idIsBiInv j c h x) k = ƛ h k (id c j x)

id' : {a : Level}
    → {i : Size}
    → (j : Size< i)
    → {G : GlobSet a i}
    → (c : Composable i G)
    → (h : HCat G c)
    → (x : cells G)
    → BiInvertibleCell i c j x x
cell (id' j c h x) = id c j x
biInv (id' j c h x) = idIsBiInv j c h x

record BiInvertComp {a b c : Level}
                    (i : Size)
                    (j : Size< i)
                    {A : GlobSet a i}
                    {B : GlobSet b i}
                    {C : GlobSet c i}
                    {x x' : cells A}
                    {y y' : cells B}
                    {z z' : cells C}
                    (cA : Composable i A)
                    (cB : Composable i B)
                    (cC : Composable i C)
                    (composition : GlobSetMorphism (morphisms A j x x'
                                                    ×G
                                                    morphisms B j y y')
                                                   (morphisms C j z z')) : Set (suc (a ⊔ b ⊔ c)) where
  coinductive
  field
    biComp : {f : cells (morphisms A j x x')}
           → {g : cells (morphisms B j y y')}
           → BiInvertible i cA j f
           → BiInvertible i cB j g
           → BiInvertible i cC j (func composition (f , g))
    biCompHigher : (k : Size< j)
                 → (f f' : cells (morphisms A j x x'))
                 → (g g' : cells (morphisms B j y y'))
                 → BiInvertComp j k (compHigher cA j x x') (compHigher cB j y y') (compHigher cC j z z')
                                  (funcMorphisms composition k (f , g) (f' , g'))

open BiInvertComp

compBiInv : {a : Level}
            {i : Size}
          → (j : Size< i)
            {G : GlobSet a i}
          → (c : Composable i G)
          → (h : HCat G c)
          → (x y z : cells G)
          → BiInvertComp i j c c c (comp c j x y z)

generateBiComp : {a b c : Level}
               → (i : Size)
               → (j : Size< i)
               → (k : Size< j)
               → {A : GlobSet a i}
               → {B : GlobSet b i}
               → {C : GlobSet c i}
               → {x x' : cells A}
               → {y y' : cells B}
               → {z z' : cells C}
               → (cA : Composable i A)
               → (cB : Composable i B)
               → (cC : Composable i C)
               → HCat C cC
               → (composition : GlobSetMorphism (morphisms A j x x'
                                                 ×G
                                                 morphisms B j y y')
                                                (morphisms C j z z'))
               → PreserveComp (prodComp (compHigher cA j x x') (compHigher cB j y y')) (compHigher cC j z z') composition
               → PreserveIden (prodComp (compHigher cA j x x') (compHigher cB j y y')) (compHigher cC j z z') composition
               → (f f' : cells (morphisms A j x x'))
               → (g g' : cells (morphisms B j y y'))
               → BiInvertComp j
                              k
                              (compHigher cA j x x')
                              (compHigher cB j y y')
                              (compHigher cC j z z')
                              (funcMorphisms composition k (f , g) (f' , g'))

comp1BiInv : {a : Level}
           → {i : Size}
           → {G : GlobSet a i}
           → (c : Composable i G)
           → HCat G c
           → {x y z : cells G}
           → {j : Size< i}
           → {f : cells (morphisms G j x y)}
           → {g : cells (morphisms G j y z)}
           → BiInvertible i c j f
           → BiInvertible i c j g
           → BiInvertible i c j (comp1 c f g)
comp1BiInv c h {x} {y} {z} {j} bf bg = biComp (compBiInv j c h x y z) bf bg

comp2BiInv : {a : Level}
           → {i : Size}
           → {G : GlobSet a i}
           → (c : Composable i G)
           → HCat G c
           → {x y z : cells G}
           → {j : Size< i}
           → {f f' : cells (morphisms G j x y)}
           → {g g' : cells (morphisms G j y z)}
           → {k : Size< j}
           → {α : cells (morphisms (morphisms G j x y) k f f')}
           → {β : cells (morphisms (morphisms G j y z) k g g')}
           → BiInvertible j (compHigher c j x y) k α
           → BiInvertible j (compHigher c j y z) k β
           → BiInvertible j (compHigher c j x z) k (comp2 c α β)
comp2BiInv c h {x} {y} {z} {j} {f} {f'} {g} {g'} {k} bα bβ =
  biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') bα bβ

comp3BiInv : {a : Level}
           → {i : Size}
           → {G : GlobSet a i}
           → (c : Composable i G)
           → HCat G c
           → {x y z : cells G}
           → {j : Size< i}
           → {f f' : cells (morphisms G j x y)}
           → {g g' : cells (morphisms G j y z)}
           → {k : Size< j}
           → {α α' : cells (morphisms (morphisms G j x y) k f f')}
           → {β β' : cells (morphisms (morphisms G j y z) k g g')}
           → {l : Size< k}
           → {δ : cells (morphisms (morphisms (morphisms G j x y) k f f') l α α')}
           → {ε : cells (morphisms (morphisms (morphisms G j y z) k g g') l β β')}
           → BiInvertible k (compHigher (compHigher c j x y) k f f') l δ
           → BiInvertible k (compHigher (compHigher c j y z) k g g') l ε
           → BiInvertible k (compHigher (compHigher c j x z)
                                        k
                                        (comp1 c f g)
                                        (comp1 c f' g'))
                            l
                            (comp3 c δ ε)
comp3BiInv c h {x} {y} {z} {j} {f} {f'} {g} {g'} {k} {α} {α'} {β} {β'} {l} bδ bε =
  biComp (biCompHigher (biCompHigher (compBiInv j c h x y z) k f f' g g') l α α' β β') bδ bε

comp1' : {a : Level}
       → {i : Size}
       → {G : GlobSet a i}
       → (c : Composable i G)
       → HCat G c
       → {j : Size< i}
       → {x y z : cells G}
       → BiInvertibleCell i c j x y
       → BiInvertibleCell i c j y z
       → BiInvertibleCell i c j x z
cell (comp1' c h f g) = comp1 c (cell f) (cell g)
biInv (comp1' c h f g) = comp1BiInv c h (biInv f) (biInv g)

comp2' : {a : Level}
       → {i : Size}
       → {G : GlobSet a i}
       → (c : Composable i G)
       → HCat G c
       → {j : Size< i}
       → {k : Size< j}
       → {x y z : cells G}
       → {f f' : cells (morphisms G j x y)}
       → {g g' : cells (morphisms G j y z)}
       → BiInvertibleCell j (compHigher c j x y) k f f'
       → BiInvertibleCell j (compHigher c j y z) k g g'
       → BiInvertibleCell j (compHigher c j x z) k (comp1 c f g) (comp1 c f' g')
cell (comp2' c h α β) = comp2 c (cell α) (cell β)
biInv (comp2' c h α β) = comp2BiInv c h (biInv α) (biInv β)

comp3' : {a : Level}
       → {i : Size}
       → {G : GlobSet a i}
       → (c : Composable i G)
       → HCat G c
       → {j : Size< i}
       → {k : Size< j}
       → {l : Size< k}
       → {x y z : cells G}
       → {f f' : cells (morphisms G j x y)}
       → {g g' : cells (morphisms G j y z)}
       → {α α' : cells (morphisms (morphisms G j x y) k f f')}
       → {β β' : cells (morphisms (morphisms G j y z) k g g')}
       → BiInvertibleCell k (compHigher (compHigher c j x y) k f f') l α α'
       → BiInvertibleCell k (compHigher (compHigher c j y z) k g g') l β β'
       → BiInvertibleCell k (compHigher (compHigher c j x z)
                                        k
                                        (comp1 c f g)
                                        (comp1 c f' g'))
                            l
                            (comp2 c α β)
                            (comp2 c α' β')
cell (comp3' c h δ ε) = comp3 c (cell δ) (cell ε)
biInv (comp3' c h δ ε) = comp3BiInv c h (biInv δ) (biInv ε)


f* (biComp (generateBiComp i j k cA cB cC h composition prevComp prevId f f' g g') bα bβ) = func (funcMorphisms composition k (f' , g') (f , g)) ((f* bα) , (f* bβ))
*f (biComp (generateBiComp i j k cA cB cC h composition prevComp prevId f f' g g') bα bβ) = func (funcMorphisms composition k (f' , g') (f , g)) ((*f bα) , (*f bβ))
fR (biComp (generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB cC h composition prevComp prevId f f' g g') {α} {β} bα bβ) l = {!!}
  -- comp1 (compHigher (compHigher cC j z z') k (func composition (f , g)) (func composition (f , g)))
  --       (comp1 (compHigher (compHigher cC j z z') k (func composition (f , g)) (func composition (f , g)))
  --              (eq (compPreserve prevComp k l (f , g) (f' , g') (f , g)) l ((α , β) , f* bα , f* bβ))
  --              (func (funcMorphisms (funcMorphisms composition
  --                                                  k
  --                                                  (f , g)
  --                                                  (f , g))
  --                                   l
  --                                   (comp1 (compHigher cA j x x')
  --                                          α
  --                                          (f* bα)
  --                                    ,
  --                                    comp1 (compHigher cB j y y')
  --                                          β
  --                                          (f* bβ))
  --                                   ((id (compHigher cA j x x') k f)
  --                                    ,
  --                                    (id (compHigher cB j y y') k g)))
  --                    ((fR bα l) , (fR bβ l))))
  --       (idPreserve prevId k l (f , g))
fL (biComp (generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB cC h composition prevComp prevId f f' g g') {α} {β} bα bβ) l = {!!}
  -- comp1 (compHigher (compHigher cC j z z') k (func composition (f' , g')) (func composition (f' , g')))
  --       (comp1 (compHigher (compHigher cC j z z') k (func composition (f' , g')) (func composition (f' , g')))
  --              (eq (compPreserve prevComp k l (f' , g') (f , g) (f' , g')) l ((*f bα , *f bβ) , α , β))
  --              (func (funcMorphisms (funcMorphisms composition
  --                                                  k
  --                                                  (f' , g')
  --                                                  (f' , g'))
  --                                   l
  --                                   (comp1 (compHigher cA j x x')
  --                                          (*f bα)
  --                                          α
  --                                    ,
  --                                    comp1 (compHigher cB j y y')
  --                                          (*f bβ)
  --                                          β)
  --                                   (id (compHigher cA j x x') k f'
  --                                    ,
  --                                    id (compHigher cB j y y') k g'))
  --                    ((fL bα l) , fL bβ l)))
  --       (idPreserve prevId k l (f' , g'))
-- fRBiInv (biComp (generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB cC h composition prevComp prevId f f' g g') {α} {β} bα bβ) l =
--   biComp (compBiInv l
--                     (compHigher (compHigher cC j z z')
--                                 k
--                                 (func composition (f , g))
--                                 (func composition (f , g)))
--                     (hcoin (hcoin h j z z')
--                            k
--                            (func composition (f , g))
--                            (func composition (f , g)))
--                     (comp1 (compHigher cC j z z')
--                            (func (funcMorphisms composition
--                                                 k
--                                                 (f , g)
--                                                 (f' , g'))
--                                  (α , β))
--                            (f* (biComp (generateBiComp i
--                                                        j
--                                                        k
--                                                        cA
--                                                        cB
--                                                        cC
--                                                        h
--                                                        composition
--                                                         prevComp
--                                                        prevId
--                                                        f
--                                                        f'
--                                                        g
--                                                        g')
--                                        bα
--                                        bβ)))
--                     (func (funcMorphisms composition k (f , g) (f , g))
--                           (id (compHigher cA j x x') k f , id (compHigher cB j y y') k g))
--                     (id (compHigher cC j z z') k (func composition (f , g))))
--          (biComp (compBiInv l
--                             (compHigher (compHigher cC j z z')
--                                         k
--                                         (func composition (f , g))
--                                         (func composition (f , g)))
--                             (hcoin (hcoin h j z z')
--                                    k
--                                    (func composition (f , g))
--                                    (func composition (f , g)))
--                             (comp1 (compHigher cC j z z')
--                                     (func (funcMorphisms composition
--                                                          k
--                                                          (f , g)
--                                                          (f' , g'))
--                                           (α , β))
--                                     (f* (biComp (generateBiComp i
--                                                                 j
--                                                                 k
--                                                                 cA
--                                                                 cB
--                                                                 cC
--                                                                 h
--                                                                 composition
--                                                                 prevComp
--                                                                 prevId
--                                                                 f
--                                                                 f'
--                                                                 g
--                                                                 g')
--                                                 bα
--                                                 bβ)))
--                             (func (gComp (funcMorphisms composition
--                                                         k
--                                                         (f , g)
--                                                         (f , g))
--                                          (comp (prodComp (compHigher cA j x x')
--                                                          (compHigher cB j y y'))
--                                                k
--                                                (f , g)
--                                                (f' , g')
--                                                (f , g)))
--                                   ((α , β) , f* bα , f* bβ))
--                             (func (funcMorphisms composition k (f , g) (f , g))
--                                   (id (compHigher cA j x x') k f , id (compHigher cB j y y') k g)))
--                  (eqBiInv (compPreserve prevComp k l (f , g) (f' , g') (f , g))
--                           l
--                           ((α , β) , f* bα , f* bβ))
--                  (biComp (generateBiComp j
--                                          k
--                                          l
--                                          (compHigher cA j x x')
--                                          (compHigher cB j y y')
--                                          (compHigher cC j z z')
--                                          (hcoin h j z z')
--                                          (funcMorphisms composition k (f , g) (f , g))
--                                          (compPreserveCoin prevComp k (f , g) (f , g))
--                                          (idPreserveCoin prevId k (f , g) (f , g))
--                                          (func (comp (compHigher cA j x x') k f f' f)
--                                            (proj₁
--                                             (func
--                                              (interchangeG (morphisms (morphisms A j x x') k f f')
--                                               (morphisms (morphisms B j y y') k g g')
--                                               (morphisms (morphisms A j x x') k f' f)
--                                               (morphisms (morphisms B j y y') k g' g))
--                                              ((α , β) , f* bα , f* bβ))))
--                                          (id (compHigher cA j x x') k f)
--                                          (func (comp (compHigher cB j y y') k g g' g)
--                                            (proj₂
--                                             (func
--                                              (interchangeG (morphisms (morphisms A j x x') k f f')
--                                               (morphisms (morphisms B j y y') k g g')
--                                               (morphisms (morphisms A j x x') k f' f)
--                                               (morphisms (morphisms B j y y') k g' g))
--                                              ((α , β) , f* bα , f* bβ))))
--                                          (id (compHigher cB j y y') k g))
--                          (fRBiInv bα l)
--                          (fRBiInv bβ l)))
--          (idPreserveBiInv prevId k l (f , g))
-- fLBiInv (biComp (generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB cC h composition prevComp prevId f f' g g') {α} {β} bα bβ) l =
--   biComp (compBiInv l
--                     (compHigher (compHigher cC j z z')
--                                 k
--                                 (func composition (f' , g'))
--                                 (func composition (f' , g')))
--                     (hcoin (hcoin h j z z')
--                            k
--                            (func composition (f' , g'))
--                            (func composition (f' , g')))
--                     (comp1 (compHigher cC j z z')
--                            (*f (biComp (generateBiComp i
--                                                        j
--                                                        k
--                                                        cA
--                                                        cB
--                                                        cC
--                                                        h
--                                                        composition
--                                                        prevComp
--                                                        prevId
--                                                        f
--                                                        f'
--                                                        g
--                                                        g')
--                                        bα
--                                        bβ))
--                            (func (funcMorphisms composition k (f , g) (f' , g')) (α , β)))
--                     (func (funcMorphisms composition
--                                          k
--                                          (f' , g')
--                                          (f' , g'))
--                           (id (compHigher cA j x x') k f' , id (compHigher cB j y y') k g'))
--                     (id (compHigher cC j z z') k (func composition (f' , g'))))
--          (biComp (compBiInv l
--                             (compHigher (compHigher cC j z z')
--                                         k
--                                         (func composition (f' , g'))
--                                         (func composition (f' , g')))
--                             (hcoin (hcoin h j z z')
--                                    k
--                                    (func composition (f' , g'))
--                                    (func composition (f' , g')))
--                             (comp1 (compHigher cC j z z')
--                                    (*f (biComp (generateBiComp i
--                                                                j
--                                                                k
--                                                                cA
--                                                                cB
--                                                                cC
--                                                                h
--                                                                composition
--                                                                prevComp
--                                                                prevId
--                                                                f
--                                                                f'
--                                                                g
--                                                                g')
--                                                bα
--                                                bβ))
--                                    (func (funcMorphisms composition k (f , g) (f' , g')) (α , β)))
--                             (func (gComp (funcMorphisms composition
--                                                         k
--                                                         (f' , g')
--                                                         (f' , g'))
--                                          (comp (prodComp (compHigher cA j x x')
--                                                          (compHigher cB j y y'))
--                                                k
--                                                (f' , g')
--                                                (f , g)
--                                                (f' , g')))
--                                   ((*f bα , *f bβ) , α , β))
--                             (func (funcMorphisms composition
--                                                  k
--                                                  (f' , g')
--                                                  (f' , g'))
--                                   (id (compHigher cA j x x') k f'
--                                    ,
--                                    id (compHigher cB j y y') k g')))
--                  (eqBiInv (compPreserve prevComp
--                                         k
--                                         l
--                                         (f' , g')
--                                         (f , g)
--                                         (f' , g'))
--                           l
--                           ((*f bα , *f bβ) , α , β))
--                  (biComp (generateBiComp j
--                                          k
--                                          l
--                                          (compHigher cA j x x')
--                                          (compHigher cB j y y')
--                                          (compHigher cC j z z')
--                                          (hcoin h j z z')
--                                          (funcMorphisms composition k (f' , g') (f' , g'))
--                                          (compPreserveCoin prevComp
--                                                            k
--                                                            (f' , g')
--                                                            (f' , g'))
--                                          (idPreserveCoin prevId
--                                                          k
--                                                          (f' , g')
--                                                          (f' , g'))
--                                          (func (comp (compHigher cA j x x') k f' f f')
--                                            (proj₁
--                                             (func
--                                              (interchangeG (morphisms (morphisms A j x x') k f' f)
--                                               (morphisms (morphisms B j y y') k g' g)
--                                               (morphisms (morphisms A j x x') k f f')
--                                               (morphisms (morphisms B j y y') k g g'))
--                                              ((*f bα , *f bβ) , α , β))))
--                                          (id (compHigher cA j x x') k f')
--                                          (func (comp (compHigher cB j y y') k g' g g')
--                                            (proj₂
--                                             (func
--                                              (interchangeG (morphisms (morphisms A j x x') k f' f)
--                                               (morphisms (morphisms B j y y') k g' g)
--                                               (morphisms (morphisms A j x x') k f f')
--                                               (morphisms (morphisms B j y y') k g g'))
--                                              ((*f bα , *f bβ) , α , β))))
--                                          (id (compHigher cB j y y') k g'))
--                          (fLBiInv bα l)
--                          (fLBiInv bβ l)))
--          (idPreserveBiInv prevId k l (f' , g'))
biCompHigher (generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB cC h composition prevComp prevId f f' g g') l =
  generateBiComp j
                 k
                 l
                 (compHigher cA j x x')
                 (compHigher cB j y y')
                 (compHigher cC j z z')
                 (hcoin h j z z')
                 (funcMorphisms composition k (f , g) (f' , g'))
                 (compPreserveCoin prevComp k (f , g) (f' , g'))
                 (idPreserveCoin prevId k (f , g) (f' , g'))


f* (biComp (compBiInv j c h x y z) bf bg) = comp1 c (f* bg) (f* bf)
*f (biComp (compBiInv j c h x y z) bf bg) = comp1 c (*f bg) (*f bf)
fR (biComp (compBiInv j c h x y z) {f} {g} bf bg) k = {!!}
  -- comp1 (compHigher c j x x)
  --       (assoc h f g (f* bg) (f* bf))
  --       (comp1 (compHigher c j x x)
  --              (comp2 c
  --                     (id (compHigher c j x y) k f)
  --                     (comp2 c
  --                            (fR bg k)
  --                            (id (compHigher c j y x) k (f* bf))))
  --              (comp1 (compHigher c j x x)
  --                     (comp2 c
  --                            (id (compHigher c j x y) k f)
  --                            (ƛ h k (f* bf)))
  --                     (fR bf k)))
fL (biComp (compBiInv j c h x y z) {f} {g} bf bg) k = {!!}
  -- comp1 (compHigher c j z z)
  --       (assoc h (*f bg) (*f bf) f g)
  --       (comp1 (compHigher c j z z)
  --              (comp2 c
  --                     (id (compHigher c j z y) k (*f bg))
  --                     (comp2 c
  --                            (fL bf k)
  --                            (id (compHigher c j y z) k g)))
  --              (comp1 (compHigher c j z z)
  --                     (comp2 c
  --                            (id (compHigher c j z y) k (*f bg))
  --                            (ƛ h k g))
  --                     (fL bg k)))
-- fRBiInv (biComp (compBiInv {i = i} j c h x y z) {f} {g} bf bg) k =
--   biComp (compBiInv k
--                     (compHigher c j x x)
--                     (hcoin h j x x)
--                     (comp1 c
--                            (comp1 c f g)
--                            (comp1 c (f* bg) (f* bf)))
--                            (comp1 c f (comp1 c (comp1 c g (f* bg)) (f* bf)))
--                            (id c j x))
--          (assocBiInv h f g (f* bg) (f* bf))
--          (biComp (compBiInv k
--                             (compHigher c j x x)
--                             (hcoin h j x x)
--                             (func (comp c j x y x) (f , func (comp c j y y x) (func (comp c j y z y) (g , f* bg) , f* bf)))
--                             (comp1 c f (comp1 c (id c j y) (f* bf))) (id c j x))
--                  (biComp (generateBiComp i
--                                          j
--                                          k
--                                          c
--                                          c
--                                          c
--                                          h
--                                          (comp c j x y x)
--                                          (compPreserveComp h j x y x)
--                                          (compPreserveId h j x y x)
--                                          f
--                                          f
--                                          (func (comp c j y y x) (func (comp c j y z y) (g , f* bg) , f* bf))
--                                          (func (comp c j y y x) (id c j y , f* bf)))
--                          (idIsBiInv k (compHigher c j x y) (hcoin h j x y) f)
--                          (biComp (generateBiComp i
--                                                  j
--                                                  k
--                                                  c
--                                                  c
--                                                  c
--                                                  h
--                                                  (comp c j y y x)
--                                                  (compPreserveComp h j y y x)
--                                                  (compPreserveId h j y y x)
--                                                  (comp1 c g (f* bg))
--                                                  (id c j y)
--                                                  (f* bf)
--                                                  (f* bf))
--                                  (fRBiInv bg k)
--                                  (idIsBiInv k (compHigher c j y x) (hcoin h j y x) (f* bf))))
--                  (biComp (compBiInv k (compHigher c j x x)
--                                       (hcoin h j x x)
--                                       (func (comp c j x y x)
--                                             (f , func (comp c j y y x) (id c j y , f* bf)))
--                                       (comp1 c f (f* bf))
--                                       (id c j x))
--                          (biComp (generateBiComp i
--                                                  j
--                                                  k
--                                                  c
--                                                  c
--                                                  c
--                                                  h
--                                                  (comp c j x y x)
--                                                  (compPreserveComp h j x y x)
--                                                  (compPreserveId h j x y x)
--                                                  f
--                                                  f
--                                                  (comp1 c (id c j y) (f* bf))
--                                                  (f* bf))
--                                  (idIsBiInv k (compHigher c j x y) (hcoin h j x y) f)
--                                  (ƛBiInv h k (f* bf)))
--                          (fRBiInv bf k)))

-- fLBiInv (biComp (compBiInv {i = i} j c h x y z) {f} {g} bf bg) k =
--   biComp (compBiInv k
--                     (compHigher c j z z)
--                     (hcoin h j z z)
--                     (comp1 c (*f (biComp (compBiInv j c h x y z) bf bg))
--                       (func (comp c j x y z) (f , g)))
--                     (comp1 c (*f bg) (comp1 c (comp1 c (*f bf) f) g))
--                     (id c j z))
--          (assocBiInv h (*f bg) (*f bf) f g)
--          (biComp (compBiInv k
--                             (compHigher c j z z)
--                             (hcoin h j z z)
--                             (func (comp c j z y z)
--                               (*f bg ,
--                                func (comp c j y y z) (func (comp c j y x y) (*f bf , f) , g)))
--                             (comp1 c (*f bg) (comp1 c (id c j y) g))
--                             (id c j z))
--                  (biComp (generateBiComp i
--                                          j
--                                          k
--                                          c
--                                          c
--                                          c
--                                          h
--                                          (comp c j z y z)
--                                          (compPreserveComp h j z y z)
--                                          (compPreserveId h j z y z)
--                                          (*f bg)
--                                          (*f bg)
--                                          (func (comp c j y y z) (func (comp c j y x y) (*f bf , f) , g))
--                                          (func (comp c j y y z) (id c j y , g)))
--                          (idIsBiInv k (compHigher c j z y) (hcoin h j z y) (*f bg))
--                          (biComp (generateBiComp i
--                                                  j
--                                                  k
--                                                  c
--                                                  c
--                                                  c
--                                                  h
--                                                  (comp c j y y z)
--                                                  (compPreserveComp h j y y z)
--                                                  (compPreserveId h j y y z)
--                                                  (func (comp c j y x y) (*f bf , f))
--                                                  (id c j y)
--                                                  g
--                                                  g)
--                                  (fLBiInv bf k)
--                                  (idIsBiInv k (compHigher c j y z) (hcoin h j y z) g)))
--                  (biComp (compBiInv k
--                                     (compHigher c j z z)
--                                     (hcoin h j z z)
--                                     (func (comp c j z y z)
--                                           (*f bg , func (comp c j y y z) (id c j y , g)))
--                                     (comp1 c (*f bg) g)
--                                     (id c j z))
--                          (biComp (generateBiComp i
--                                                  j
--                                                  k
--                                                  c
--                                                  c
--                                                  c
--                                                  h
--                                                  (comp c j z y z)
--                                                  (compPreserveComp h j z y z)
--                                                  (compPreserveId h j z y z)
--                                                  (*f bg)
--                                                  (*f bg)
--                                                  (func (comp c j y y z) (id c j y , g))
--                                                  g)
--                                  (idIsBiInv k (compHigher c j z y) (hcoin h j z y) (*f bg))
--                                  (ƛBiInv h k g))
--                          (fLBiInv bg k)))
biCompHigher (compBiInv {i = i} j c h x y z) k f f' g g' =
  generateBiComp i
                 j
                 k
                 c
                 c
                 c
                 h
                 (comp c j x y z)
                 (compPreserveComp h j x y z)
                 (compPreserveId h j x y z)
                 f
                 f'
                 g
                 g'
