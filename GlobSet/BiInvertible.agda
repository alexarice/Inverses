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
            (h : HigherCat i G)
          → (x : cells G)
          → BiInvertible i (com h) j (id (com h) j x)
f* (idIsBiInv j h x) = id (com h) j x
*f (idIsBiInv j h x) = id (com h) j x
fR (idIsBiInv j h x) k = ƛ (hCat h) k (id (com h) j x)
fL (idIsBiInv j h x) k = ƛ (hCat h) k (id (com h) j x)

id' : {a : Level}
    → {i : Size}
    → {G : GlobSet a i}
    → (h : HigherCat i G)
    → (j : Size< i)
    → (x : cells G)
    → BiInvertibleCell i (com h) j x x
cell (id' h j x) = id (com h) j x
biInv (id' h j x) = idIsBiInv j h x

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
          → (h : HigherCat i G)
          → (x y z : cells G)
          → BiInvertComp i j (com h) (com h) (com h) (comp (com h) j x y z)

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
               → (hC : HigherCat i C)
               → (composition : GlobSetMorphism (morphisms A j x x'
                                                 ×G
                                                 morphisms B j y y')
                                                (morphisms C j z z'))
               → PreserveComp (prodComp (compHigher cA j x x') (compHigher cB j y y')) (compHigher (com hC) j z z') composition
               → PreserveIden (prodComp (compHigher cA j x x') (compHigher cB j y y')) (compHigher (com hC) j z z') composition
               → (f f' : cells (morphisms A j x x'))
               → (g g' : cells (morphisms B j y y'))
               → BiInvertComp j
                              k
                              (compHigher cA j x x')
                              (compHigher cB j y y')
                              (compHigher (com hC) j z z')
                              (funcMorphisms composition k (f , g) (f' , g'))

comp1BiInv : {a : Level}
           → {i : Size}
           → {G : GlobSet a i}
           → (h : HigherCat i G)
           → {x y z : cells G}
           → {j : Size< i}
           → {f : cells (morphisms G j x y)}
           → {g : cells (morphisms G j y z)}
           → BiInvertible i (com h) j f
           → BiInvertible i (com h) j g
           → BiInvertible i (com h) j (comp1 (com h) f g)
comp1BiInv h {x} {y} {z} {j} bf bg = biComp (compBiInv j h x y z) bf bg

comp2BiInv : {a : Level}
           → {i : Size}
           → {G : GlobSet a i}
           → (h : HigherCat i G)
           → {x y z : cells G}
           → {j : Size< i}
           → {f f' : cells (morphisms G j x y)}
           → {g g' : cells (morphisms G j y z)}
           → {k : Size< j}
           → {α : cells (morphisms (morphisms G j x y) k f f')}
           → {β : cells (morphisms (morphisms G j y z) k g g')}
           → BiInvertible j (compHigher (com h) j x y) k α
           → BiInvertible j (compHigher (com h) j y z) k β
           → BiInvertible j (compHigher (com h) j x z) k (comp2 (com h) α β)
comp2BiInv {a} {i} h {x} {y} {z} {j} {f} {f'} {g} {g'} {k} bα bβ =
  -- Messy definition to make termination checking work
  biComp (generateBiComp i
                         j
                         k
                         (com h)
                         (com h)
                         h
                         (comp (com h) j x y z)
                         (compPreserveComp (hCat h) j x y z)
                         (compPreserveId (hCat h) j x y z)
                         f
                         f'
                         g
                         g')
         bα
         bβ

comp3BiInv : {a : Level}
           → {i : Size}
           → {G : GlobSet a i}
           → (h : HigherCat i G)
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
           → BiInvertible k (compHigher (compHigher (com h) j x y) k f f') l δ
           → BiInvertible k (compHigher (compHigher (com h) j y z) k g g') l ε
           → BiInvertible k (compHigher (compHigher (com h) j x z)
                                        k
                                        (comp1 (com h) f g)
                                        (comp1 (com h) f' g'))
                            l
                            (comp3 (com h) δ ε)
comp3BiInv h {x} {y} {z} {j} {f} {f'} {g} {g'} {k} {α} {α'} {β} {β'} {l} bδ bε =
  biComp (biCompHigher (biCompHigher (compBiInv j h x y z) k f f' g g') l α α' β β') bδ bε

comp1' : {a : Level}
       → {i : Size}
       → {G : GlobSet a i}
       → (h : HigherCat i G)
       → {j : Size< i}
       → {x y z : cells G}
       → BiInvertibleCell i (com h) j x y
       → BiInvertibleCell i (com h) j y z
       → BiInvertibleCell i (com h) j x z
cell (comp1' h f g) = comp1 (com h) (cell f) (cell g)
biInv (comp1' h f g) = comp1BiInv h (biInv f) (biInv g)

comp2' : {a : Level}
       → {i : Size}
       → {G : GlobSet a i}
       → (h : HigherCat i G)
       → {j : Size< i}
       → {k : Size< j}
       → {x y z : cells G}
       → {f f' : cells (morphisms G j x y)}
       → {g g' : cells (morphisms G j y z)}
       → BiInvertibleCell j (compHigher (com h) j x y) k f f'
       → BiInvertibleCell j (compHigher (com h) j y z) k g g'
       → BiInvertibleCell j (compHigher (com h) j x z) k (comp1 (com h) f g) (comp1 (com h) f' g')
cell (comp2' h α β) = comp2 (com h) (cell α) (cell β)
biInv (comp2' h α β) = comp2BiInv h (biInv α) (biInv β)

comp3' : {a : Level}
       → {i : Size}
       → {G : GlobSet a i}
       → (h : HigherCat i G)
       → {j : Size< i}
       → {k : Size< j}
       → {l : Size< k}
       → {x y z : cells G}
       → {f f' : cells (morphisms G j x y)}
       → {g g' : cells (morphisms G j y z)}
       → {α α' : cells (morphisms (morphisms G j x y) k f f')}
       → {β β' : cells (morphisms (morphisms G j y z) k g g')}
       → BiInvertibleCell k (compHigher (compHigher (com h) j x y) k f f') l α α'
       → BiInvertibleCell k (compHigher (compHigher (com h) j y z) k g g') l β β'
       → BiInvertibleCell k (compHigher (compHigher (com h) j x z)
                                        k
                                        (comp1 (com h) f g)
                                        (comp1 (com h) f' g'))
                            l
                            (comp2 (com h) α β)
                            (comp2 (com h) α' β')
cell (comp3' h δ ε) = comp3 (com h) (cell δ) (cell ε)
biInv (comp3' h δ ε) = comp3BiInv h (biInv δ) (biInv ε)


f* (biComp (generateBiComp i j k cA cB hC composition prevComp prevId f f' g g') bα bβ) = func (funcMorphisms composition k (f' , g') (f , g)) ((f* bα) , (f* bβ))
*f (biComp (generateBiComp i j k cA cB hC composition prevComp prevId f f' g g') bα bβ) = func (funcMorphisms composition k (f' , g') (f , g)) ((*f bα) , (*f bβ))
fR (biComp (generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB hC composition prevComp prevId f f' g g') {α} {β} bα bβ) l =
  comp1' (coin (coin hC j z z') k (func composition (f , g)) (func composition (f , g)))
         (comp1' (coin (coin hC j z z') k (func composition (f , g)) (func composition (f , g)))
                 (eq (compPreserve prevComp k l (f , g) (f' , g') (f , g)) l ((α , β) , f* bα , f* bβ))
                 (record {
                   cell = func (funcMorphisms (funcMorphisms composition
                                                             k
                                                             (f , g)
                                                             (f , g))
                                              l
                                              (comp1 (compHigher cA j x x') α (f* bα)
                                               ,
                                               comp1 (compHigher cB j y y') β (f* bβ))
                                              (id (compHigher cA j x x') k f
                                               ,
                                               id (compHigher cB j y y') k g))
                               ((cell (fR bα l)) , (cell (fR bβ l))) ;
                   biInv = biComp (generateBiComp j
                                                  k
                                                  l
                                                  (compHigher cA j x x')
                                                  (compHigher cB j y y')
                                                  (coin hC j z z')
                                                  (funcMorphisms composition k (f , g) (f , g))
                                                  (compPreserveCoin prevComp k (f , g) (f , g))
                                                  (idPreserveCoin prevId k (f , g) (f , g))
                                                  (comp1 (compHigher cA j x x') α (f* bα))
                                                  (id (compHigher cA j x x') k f)
                                                  (comp1 (compHigher cB j y y') β (f* bβ))
                                                  (id (compHigher cB j y y') k g))
                                  (biInv (fR bα l))
                                  (biInv (fR bβ l)) }))
         (idPreserve prevId k l (f , g))
fL (biComp (generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB hC composition prevComp prevId f f' g g') {α} {β} bα bβ) l =
  comp1' (coin (coin hC j z z') k (func composition (f' , g')) (func composition (f' , g')))
         (comp1' (coin (coin hC j z z') k (func composition (f' , g')) (func composition (f' , g')))
                 (eq (compPreserve prevComp k l (f' , g') (f , g) (f' , g')) l ((*f bα , *f bβ) , α , β))
                 (record {
                   cell = func (funcMorphisms (funcMorphisms composition
                                                             k
                                                             (f' , g')
                                                             (f' , g'))
                                              l
                                              (comp1 (compHigher cA j x x') (*f bα) α
                                               ,
                                               comp1 (compHigher cB j y y') (*f bβ) β)
                                              (id (compHigher cA j x x') k f'
                                               ,
                                               id (compHigher cB j y y') k g'))
                               ((cell (fL bα l)) , cell (fL bβ l)) ;
                   biInv = biComp (generateBiComp j
                                                  k
                                                  l
                                                  (compHigher cA j x x')
                                                  (compHigher cB j y y')
                                                  (coin hC j z z')
                                                  (funcMorphisms composition k (f' , g') (f' , g'))
                                                  (compPreserveCoin prevComp k (f' , g') (f' , g'))
                                                  (idPreserveCoin prevId k (f' , g') (f' , g'))
                                                  (comp1 (compHigher cA j x x') (*f bα) α)
                                                  (id (compHigher cA j x x') k f')
                                                  (comp1 (compHigher cB j y y') (*f bβ) β)
                                                  (id (compHigher cB j y y') k g'))
                                  (biInv (fL bα l))
                                  (biInv (fL bβ l)) }))
         (idPreserve prevId k l (f' , g'))
biCompHigher (generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB hC composition prevComp prevId f f' g g') l =
  generateBiComp j
                 k
                 l
                 (compHigher cA j x x')
                 (compHigher cB j y y')
                 (coin hC j z z')
                 (funcMorphisms composition k (f , g) (f' , g'))
                 (compPreserveCoin prevComp k (f , g) (f' , g'))
                 (idPreserveCoin prevId k (f , g) (f' , g'))


f* (biComp (compBiInv j h x y z) bf bg) = comp1 (com h) (f* bg) (f* bf)
*f (biComp (compBiInv j h x y z) bf bg) = comp1 (com h) (*f bg) (*f bf)
fR (biComp (compBiInv j h x y z) {f} {g} bf bg) k =
  comp1' (coin h j x x)
         (assoc (hCat h) f g (f* bg) (f* bf))
         (comp1' (coin h j x x)
                 (comp2' h
                         (id' (coin h j x y) k f)
                         (comp2' h
                                 (fR bg k)
                                 (id' (coin h j y x) k (f* bf))))
                 (comp1' (coin h j x x)
                         (comp2' h
                                 (id' (coin h j x y) k f)
                                 (ƛ (hCat h) k (f* bf)))
                         (fR bf k)))
fL (biComp (compBiInv j h x y z) {f} {g} bf bg) k =
  comp1' (coin h j z z)
         (assoc (hCat h) (*f bg) (*f bf) f g)
         (comp1' (coin h j z z)
                 (comp2' h
                         (id' (coin h j z y) k (*f bg))
                         (comp2' h
                                 (fL bf k)
                                 (id' (coin h j y z) k g)))
                 (comp1' (coin h j z z)
                         (comp2' h
                                 (id' (coin h j z y) k (*f bg))
                                 (ƛ (hCat h) k g))
                         (fL bg k)))
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
biCompHigher (compBiInv {i = i} j h x y z) k f f' g g' =
  generateBiComp i
                 j
                 k
                 (com h)
                 (com h)
                 h
                 (comp (com h) j x y z)
                 (compPreserveComp (hCat h) j x y z)
                 (compPreserveId (hCat h) j x y z)
                 f
                 f'
                 g
                 g'
