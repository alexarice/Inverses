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
          → BiInvertible i c j (id c j x)
f* (idIsBiInv j c h x) = id c j x
*f (idIsBiInv j c h x) = id c j x
fR (idIsBiInv j c h x) k = ƛ h k (id c j x)
fL (idIsBiInv j c h x) k = ƛ h k (id c j x)
fRBiInv (idIsBiInv j c h x) k = ƛBiInv h k (id c j x)
fLBiInv (idIsBiInv j c h x) k = ƛBiInv h k (id c j x)

record BiInvertComp (i : Size)
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

generateBiComp : (i : Size)
               → (j : Size< i)
               → (k : Size< j)
               → {A B C : GlobSet i}
               → {x x' : cells A}
               → {y y' : cells B}
               → {z z' : cells C}
               → (cA : Composable A)
               → (cB : Composable B)
               → (cC : Composable C)
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
f* (biComp (generateBiComp i j k cA cB cC composition prevComp prevId f f' g g') bα bβ) = func (funcMorphisms composition k (f' , g') (f , g)) ((f* bα) , (f* bβ))
*f (biComp (generateBiComp i j k cA cB cC composition prevComp prevId f f' g g') bα bβ) = func (funcMorphisms composition k (f' , g') (f , g)) ((*f bα) , (*f bβ))
fR (biComp (generateBiComp i j k {_} {_} {_} {x} {x'} {y} {y'} {z} {z'} cA cB cC composition prevComp prevId f f' g g') {α} {β} bα bβ) l =
  comp1 (compHigher (compHigher cC j z z') k (func composition (f , g)) (func composition (f , g)))
        (comp1 (compHigher (compHigher cC j z z') k (func composition (f , g)) (func composition (f , g)))
               (eq (compPreserve prevComp k l (f , g) (f' , g') (f , g)) l ((α , β) , f* bα , f* bβ))
               (func (funcMorphisms (funcMorphisms composition k (f , g) (f , g)) l (comp1 (compHigher cA j x x') α (f* bα) , comp1 (compHigher cB j y y') β (f* bβ)) ((id (compHigher cA j x x') k f) , (id (compHigher cB j y y') k g))) ((fR bα l) , (fR bβ l))))
        (idPreserve prevId k l (f , g))
fL (biComp (generateBiComp i j k cA cB cC composition prevComp prevId f f' g g') bα bβ) l = {!!}
fRBiInv (biComp (generateBiComp i j k cA cB cC composition prevComp prevId f f' g g') bα bβ) = {!!}
fLBiInv (biComp (generateBiComp i j k cA cB cC composition prevComp prevId f f' g g') bα bβ) = {!!}
biCompHigher (generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB cC composition prevComp prevId f f' g g') l α β α' β' = generateBiComp j k l {morphisms A j x x'} {morphisms B j y y'} {morphisms C j z z'} test {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
 where
  test : Composable (morphisms A j x x')
  test = compHigher cA j x x'

compBiInv : {i : Size}
          → (j : Size< i)
            {G : GlobSet i}
          → (c : Composable G)
          → (h : HCat G c)
          → (x y z : cells G)
          → BiInvertComp i j c c c (comp c j x y z)
f* (biComp (compBiInv j c h x y z) bf bg) = comp1 c (f* bg) (f* bf)
*f (biComp (compBiInv j c h x y z) bf bg) = comp1 c (*f bg) (*f bf)
fR (biComp (compBiInv j c h x y z) {f} {g} bf bg) k =
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
fL (biComp (compBiInv j c h x y z) {f} {g} bf bg) k =
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
fRBiInv (biComp (compBiInv j {G} c h x y z) {f} {g} bf bg) k =
  biComp (compBiInv k
                    (compHigher c j x x)
                    (hcoin h j x x)
                    (comp1 c
                           (comp1 c f g)
                           (comp1 c (f* bg) (f* bf)))
                           (comp1 c f (comp1 c (comp1 c g (f* bg)) (f* bf)))
                           (id c j x))
         (assocBiInv h f g (f* bg) (f* bf))
         (biComp (compBiInv k
                            (compHigher c j x x)
                            (hcoin h j x x)
                            (func (comp c j x y x) (f , func (comp c j y y x) (func (comp c j y z y) (g , f* bg) , f* bf)))
                            (comp1 c f (comp1 c (id c j y) (f* bf))) (id c j x))
                 (biComp (biCompHigher (compBiInv j c h x y x) k f f (func (comp c j y y x) (func (comp c j y z y) (g , f* bg) , f* bf)) (func (comp c j y y x) (id c j y , f* bf)))
                         (idIsBiInv k (compHigher c j x y) (hcoin h j x y) f)
                         (biComp (biCompHigher (compBiInv j c h y y x)
                                               k
                                               (func (comp c j y z y) (g , f* bg))
                                               (id c j y)
                                               (f* bf)
                                               (f* bf))
                                 (fRBiInv bg k)
                                 (idIsBiInv k (compHigher c j y x) (hcoin h j y x) (f* bf))))
                 (biComp (compBiInv k (compHigher c j x x) (hcoin h j x x) (func (comp c j x y x)
                                                                  (f , func (comp c j y y x) (id c j y , f* bf))) (comp1 c f (f* bf)) (id c j x))
                         (biComp (biCompHigher (compBiInv j
                                                          c
                                                          h
                                                          x
                                                          y
                                                          x)
                                               k
                                               f
                                               f
                                               (func (comp c j y y x) (id c j y , f* bf))
                                               (f* bf))
                                 (idIsBiInv k (compHigher c j x y) (hcoin h j x y) f)
                                 (ƛBiInv h k (f* bf)))
                         (fRBiInv bf k)))

fLBiInv (biComp (compBiInv j c h x y z) bf bg) k = {!!}
f* (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') bα bβ) = func (funcMorphisms (comp c j x y z) k (f' , g') (f , g)) ((f* bα) , (f* bβ))
*f (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') bα bβ) = func (funcMorphisms (comp c j x y z) k (f' , g') (f , g)) ((*f bα) , *f bβ)
fR (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') {α} {β} bα bβ) l =
  comp1 (compHigher (compHigher c j x z) k (comp1 c f g) (comp1 c f g))
        (comp1 (compHigher (compHigher c j x z) k (comp1 c f g) (comp1 c f g))
               (eq (compPreserve (compPreserveComp h j x y z) k l (f , g) (f' , g') (f , g)) l ((α , β) , f* bα , f* bβ))
               (comp3 c (fR bα l) (fR bβ l)))
        (idPreserve (compPreserveId h j) k l (f , g))
fL (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') {α} {β} bα bβ) l =
  comp1 (compHigher (compHigher c j x z) k (func (comp c j x y z) (f' , g')) (func (comp c j x y z) (f' , g')))
        (comp1 (compHigher (compHigher c j x z) k (func (comp c j x y z) (f' , g')) (func (comp c j x y z) (f' , g')))
               (eq (compPreserve (compPreserveComp h j x y z) k l (f' , g') (f , g) (f' , g')) l ((*f bα , *f bβ) , α , β))
               (comp3 c (fL bα l) (fL bβ l)))
        (idPreserve (compPreserveId h j) k l (f' , g'))
fRBiInv (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') bα bβ) l = {!!}
fLBiInv (biComp (biCompHigher (compBiInv j c h x y z) k f f' g g') bα bβ) l = {!!}
f* (biComp (biCompHigher (biCompHigher (compBiInv j c h x y z) k f f' g g') l α α' β β') bγ bζ) =
  func (funcMorphisms (funcMorphisms (comp c j x y z) k (f , g) (f' , g')) l (α' , β') (α , β)) ((f* bγ) , (f* bζ))
*f (biComp (biCompHigher (biCompHigher (compBiInv j c h x y z) k f f' g g') l α α' β β') bγ bζ) =
  func (funcMorphisms (funcMorphisms (comp c j x y z) k (f , g) (f' , g')) l (α' , β') (α , β)) ((*f bγ) , (*f bζ))
fR (biComp (biCompHigher (biCompHigher (compBiInv j c h x y z) k f f' g g') l α α' β β') {γ} {ζ} bγ bζ) m =
  comp1 (compHigher (compHigher (compHigher c j x z) k (func (comp c j x y z) (f , g)) (func (comp c j x y z) (f' , g'))) l (func (funcMorphisms (comp c j x y z) k (f , g) (f' , g')) (α , β)) (func (funcMorphisms (comp c j x y z) k (f , g) (f' , g')) (α , β)))
        (comp1 (compHigher (compHigher (compHigher c j x z) k (func (comp c j x y z) (f , g)) (func (comp c j x y z) (f' , g'))) l (func (funcMorphisms (comp c j x y z) k (f , g) (f' , g')) (α , β)) (func (funcMorphisms (comp c j x y z) k (f , g) (f' , g')) (α , β)))
               (eq (compPreserve (compPreserveCoin (compPreserveComp h j x y z) k (f , g) (f' , g')) l m (α , β) (α' , β') (α , β)) m ((γ , ζ) , f* bγ , f* bζ))
               (func (funcMorphisms (funcMorphisms (funcMorphisms (comp c j x y z)
                                                                  k
                                                                  (f , g)
                                                                  (f' , g'))
                                                   l
                                                   (α , β)
                                                   (α , β))
                                    m
                                    (comp1 (compHigher (compHigher c j x y) k f f') γ (f* bγ) , comp1 (compHigher (compHigher c j y z) k g g') ζ (f* bζ))
                                    (id (compHigher (compHigher c j x y) k f f') l α , id (compHigher (compHigher c j y z) k g g') l β))
                     ((fR bγ m) , (fR bζ m))))
        (idPreserve (idPreserveCoin (compPreserveId h j) k (f , g) (f' , g')) l m (α , β))
fL (biComp (biCompHigher (biCompHigher (compBiInv j c h x y z) k f f' g g') l α α' β β') bγ bζ) = {!!}
fRBiInv (biComp (biCompHigher (biCompHigher (compBiInv j c h x y z) k f f' g g') l α α' β β') bγ bζ) = {!!}
fLBiInv (biComp (biCompHigher (biCompHigher (compBiInv j c h x y z) k f f' g g') l α α' β β') bγ bζ) = {!!}
biCompHigher (biCompHigher (biCompHigher (compBiInv j c h x y z) k f f' g g') l α α' β β') = {!!}
