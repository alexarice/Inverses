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
            {{_ : Composable G}}
            {{_ : HCat G}}
          → (x : cells G)
          → BiInvertible j Orig (id j x)
f* (idIsBiInv j x) = id j x
*f (idIsBiInv j x) = id j x
fR (idIsBiInv j x) k = ƛ k (id j x)
fL (idIsBiInv j x) k = ƛ k (id j x)
fRBiInv (idIsBiInv j x) k = ƛBiInv k (id j x)
fLBiInv (idIsBiInv j x) k = ƛBiInv k (id j x)

record BiInvertComp {h i : Size}
                    {G : GlobSet h}
                    {{_ : Composable G}}
                    (j : Size< i)
                    (A B C : Descendant G i)
                    {x x' : cells (realise A)}
                    {y y' : cells (realise B)}
                    {z z' : cells (realise C)}
                    (composition : GlobSetMorphism (morphisms (realise A) j x x'
                                                    ×G
                                                    morphisms (realise B) j y y')
                    (morphisms (realise C) j z z')) : Set₁ where
  coinductive
  field
    biComp : {k : Size< j}
           → (f : cells (morphisms (realise A) j x x'))
           → (g : cells (morphisms (realise B) j y y'))
           → BiInvertible j A f
           → BiInvertible j B g
           → BiInvertible j C (func composition (f , g))
    biCompHigher : (k : Size< j)
                 → (f f' : cells (morphisms (realise A) j x x'))
                 → (g g' : cells (morphisms (realise B) j y y'))
                 → BiInvertComp k (Child A j x x')
                                  (Child B j y y')
                                  (Child C j z z')
                                  (funcMorphisms composition k (f , g) (f' , g'))

open BiInvertComp

compBiInv : {i : Size} (j : Size< i) {G : GlobSet i} {{_ : Composable G}} {{_ : HCat G}} (x y z : cells G) → BiInvertComp j Orig Orig Orig (comp j x y z)
f* (biComp (compBiInv j x y z) f g bf bg) = comp1 Orig (f* bg) (f* bf)
*f (biComp (compBiInv j x y z) f g bf bg) = comp1 Orig (*f bg) (*f bf)
fR (biComp (compBiInv j x y z) f g bf bg) k =
  comp1 (Child Orig j x x)
        (assoc f g (f* bg) (f* bf))
        (comp1 (Child Orig j x x)
               (comp2 Orig
                      (idd (Child Orig j x y) k f)
                      (comp2 Orig
                             (fR bg k)
                             (idd (Child Orig j y x) k (f* bf))))
               (comp1 (Child Orig j x x)
                      (comp2 Orig
                             (idd (Child Orig j x y) k f)
                             (ƛ k (f* bf)))
                      (fR bf k)))
fL (biComp (compBiInv j x y z) f g bf bg) k =
  comp1 (Child Orig j z z)
        (assoc (*f bg) (*f bf) f g)
        (comp1 (Child Orig j z z)
               (comp2 Orig
                      (idd (Child Orig j z y) k (*f bg))
                      (comp2 Orig
                             (fL bf k)
                             (idd (Child Orig j y z) k g)))
               (comp1 (Child Orig j z z)
                      (comp2 Orig
                             (idd (Child Orig j z y) k (*f bg))
                             (ƛ k g))
                      (fL bg k)))
fRBiInv (biComp (compBiInv j x y z) f g bf bg) k = ?
fLBiInv (biComp (compBiInv j x y z) f g bf bg) = {!!}
f* (biComp (biCompHigher (compBiInv j x y z) k f f' g g') α β bα bβ) = func (funcMorphisms (comp j x y z) k (f' , g') (f , g)) ((f* bα) , (f* bβ))
*f (biComp (biCompHigher (compBiInv j x y z) k f f' g g') α β bα bβ) = func (funcMorphisms (comp j x y z) k (f' , g') (f , g)) ((*f bα) , *f bβ)
fR (biComp (biCompHigher (compBiInv j x y z) k f f' g g') α β bα bβ) l =
  comp1 (Child (Child Orig j x z)
               k
               (comp1 Orig f g)
               (comp1 Orig f g))
        (comp1 (Child (Child Orig j x z)
                      k
                      (comp1 Orig f g)
                      (comp1 Orig f g))
               (interchange₁ α β (f* bα) (f* bβ))
               (comp3 Orig (fR bα l) (fR bβ l)))
        (idenManip₁ f g)
fL (biComp (biCompHigher (compBiInv j x y z) k f f' g g') α β bα bβ) l =
  comp1 (Child (Child Orig j x z)
               k
               (comp1 Orig f' g')
               (comp1 Orig f' g'))
        (comp1 (Child (Child Orig j x z)
                      k
                      (comp1 Orig f' g')
                      (comp1 Orig f' g'))
               (interchange₁ (*f bα) (*f bβ) α β)
               (comp3 Orig (fL bα l) (fL bβ l)))
        (idenManip₁ f' g')
fRBiInv (biComp (biCompHigher (compBiInv j x y z) k f f' g g') α β bα bβ) l = {!!}
fLBiInv (biComp (biCompHigher (compBiInv j x y z) k f f' g g') α β bα bβ) l = {!!}
biCompHigher (biCompHigher (compBiInv j x y z) k f f' g g') = {!!}
