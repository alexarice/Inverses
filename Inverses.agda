{-# OPTIONS --without-K --sized-types #-}

module Inverses where
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible
open import GlobSet.Descendant
open import GlobSet.HCat


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

record BiInvertComp {i : Size}
                    (j : Size< i)
                    {A B C : GlobSet i}
                    {x x' : cells A}
                    {y y' : cells B}
                    {z z' : cells C}
                    (cA : Composable A)
                    (cB : Composable B)
                    (cC : Composable C)
                    (composition : GlobSetMorphism (morphisms A j x x'
                                                    ×G
                                                    morphisms B j y y')
                                                   (morphisms C j z z')) : Set₁ where
  coinductive
  field
    biComp : {k : Size< j}
           → (f : cells (morphisms A j x x'))
           → (g : cells (morphisms B j y y'))
           → BiInvertible cA j f
           → BiInvertible cB j g
           → BiInvertible cC j (func composition (f , g))
    biCompHigher : (k : Size< j)
                 → (f f' : cells (morphisms A j x x'))
                 → (g g' : cells (morphisms B j y y'))
                 → BiInvertComp k (compHigher cA j x x') (compHigher cB j y y') (compHigher cC j z z')
                                  (funcMorphisms composition k (f , g) (f' , g'))

open BiInvertComp

compBiInv : {i : Size}
          → (j : Size< i)
            {G : GlobSet i}
          → (c : Composable G)
          → (h : HCat G c)
          → (x y z : cells G)
          → BiInvertComp j c c c (comp c j x y z)
f* (biComp (compBiInv j c h x y z) f g bf bg) = comp1 c (f* bg) (f* bf)
*f (biComp (compBiInv j c h x y z) f g bf bg) = comp1 c (*f bg) (*f bf)
fR (biComp (compBiInv j c h x y z) f g bf bg) k =
  comp1 (compHigher c j x x)
        (assoc h f g (f* bg) (f* bf))
        (comp1 (compHigher c j x x)
               (comp2 c
                      (id (compHigher c j x y) k f)
                      (comp2 c
                             (fR bg k)
                             (id (compHigher c j y x) k (f* bf))))
               (comp1 (compHigher c j x x)
                      (comp2 c
                             (id (compHigher c j x y) k f)
                             (ƛ h k (f* bf)))
                      (fR bf k)))
fL (biComp (compBiInv j c h x y z) f g bf bg) k =
  comp1 (compHigher c j z z)
        (assoc h (*f bg) (*f bf) f g)
        (comp1 (compHigher c j z z)
               (comp2 c
                      (id (compHigher c j z y) k (*f bg))
                      (comp2 c
                             (fL bf k)
                             (id (compHigher c j y z) k g)))
               (comp1 (compHigher c j z z)
                      (comp2 c
                             (id (compHigher c j z y) k (*f bg))
                             (ƛ h k g))
                      (fL bg k)))
fRBiInv (biComp (compBiInv j c h x y z) f g bf bg) k = {!!}
fLBiInv (biComp (compBiInv j c h x y z) f g bf bg) k = {!!}
f* (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') α β bα bβ) = func (funcMorphisms (comp c j x y z) k (f' , g') (f , g)) ((f* bα) , (f* bβ))
*f (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') α β bα bβ) = func (funcMorphisms (comp c j x y z) k (f' , g') (f , g)) ((*f bα) , *f bβ)
fR (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') α β bα bβ) l =
  comp1 (compHigher (compHigher c j x z) k (comp1 c f g) (comp1 c f g))
        (comp1 (compHigher (compHigher c j x z) k (comp1 c f g) (comp1 c f g))
               (interchange₁ h α β (f* bα) (f* bβ))
               (comp3 c (fR bα l) (fR bβ l)))
        (idenManip₁ h f g)
fL (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') α β bα bβ) l =
  comp1 (compHigher (compHigher c j x z) k (comp1 c f' g') (comp1 c f' g'))
        (comp1 (compHigher (compHigher c j x z) k (comp1 c f' g') (comp1 c f' g'))
               (interchange₁ h (*f bα) (*f bβ) α β)
               (comp3 c (fL bα l) (fL bβ l)))
        (idenManip₁ h f' g')
fRBiInv (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') α β bα bβ) l = {!!}
fLBiInv (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') α β bα bβ) l = {!!}
biCompHigher (biCompHigher (compBiInv j c h x y z) k f f' g g') = {!!}
