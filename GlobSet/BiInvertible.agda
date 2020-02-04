{-# OPTIONS --without-K --sized-types --safe #-}

module GlobSet.BiInvertible where
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible.Core public
import GlobSet.Invertible as Inv
open import GlobSet.HCat

invToBiInv : {a : Level}
           → {i : Size}
           → (j : Size< i)
           → {G : GlobSet a i}
           → (c : Composable i G)
           → {x y : cells G}
           → {f : cells (morphisms G j x y)}
           → Inv.Invertible i c j f
           → BiInvertible i c j f
invToBiInv j c inv .f* = Inv.finv inv
invToBiInv j c inv .*f = Inv.finv inv
invToBiInv j c inv .fR k .cell = Inv.cell (Inv.fR inv k)
invToBiInv j c {x} inv .fR k .biInv = invToBiInv k (compHigher c j x x) (Inv.invert (Inv.fR inv k))
invToBiInv j c inv .fL k .cell = Inv.cell (Inv.fL inv k)
invToBiInv j c {x} {y} inv .fL k .biInv = invToBiInv k (compHigher c j y y) (Inv.invert (Inv.fL inv k))

invToBiInvCell : {a : Level}
               → {i : Size}
               → (j : Size< i)
               → {G : GlobSet a i}
               → {c : Composable i G}
               → {x y : cells G}
               → Inv.InvertibleCell i c j x y
               → BiInvertibleCell i c j x y
invToBiInvCell j inv .cell = Inv.cell inv
invToBiInvCell j {c = c} inv .biInv = invToBiInv j c (Inv.invert inv)


id' : {a : Level}
    → {i : Size}
    → {G : GlobSet a i}
    → (h : HigherCat i G)
    → (j : Size< i)
    → (x : cells G)
    → BiInvertibleCell i (com h) j x x
id' h j x = invToBiInvCell j (Inv.id' j h x)

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
comp1' h f g .cell = comp1 (com h) (cell f) (cell g)
comp1' h f g .biInv = comp1BiInv h (biInv f) (biInv g)

comp1-2 : {a : Level}
        → {i : Size}
        → {G : GlobSet a i}
        → (h : HigherCat i G)
        → {j : Size< i}
        → {x y : cells G}
        → {k : Size< j}
        → {u v w : cells (morphisms G j x y)}
        → BiInvertibleCell j (com (coin h j x y)) k u v
        → BiInvertibleCell j (com (coin h j x y)) k v w
        → BiInvertibleCell j (com (coin h j x y)) k u w
comp1-2 h {j} {x} {y} α β = comp1' (coin h j x y) α β

comp1-3 : {a : Level}
        → {i : Size}
        → {G : GlobSet a i}
        → (h : HigherCat i G)
        → {j : Size< i}
        → {x y : cells G}
        → {k : Size< j}
        → {f g : cells (morphisms G j x y)}
        → {l : Size< k}
        → {u v w : cells (morphisms (morphisms G j x y) k f g)}
        → BiInvertibleCell k (com (coin (coin h j x y) k f g)) l u v
        → BiInvertibleCell k (com (coin (coin h j x y) k f g)) l v w
        → BiInvertibleCell k (com (coin (coin h j x y) k f g)) l u w
comp1-3 h {j} {x} {y} {k} {f} {g} α β = comp1' (coin (coin h j x y) k f g) α β

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
comp2' h α β .cell = comp2 (com h) (cell α) (cell β)
comp2' h α β .biInv = comp2BiInv h (biInv α) (biInv β)

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
comp3' h δ ε .cell = comp3 (com h) (cell δ) (cell ε)
comp3' h δ ε .biInv = comp3BiInv h (biInv δ) (biInv ε)

origAssoc : {a : Level}
          → {i : Size}
          → {G : GlobSet a i}
          → (h : HigherCat i G)
          → {j : Size< i}
          → {k : Size< j}
          → {u v x y z : cells G}
          → (a : cells (morphisms G j u v))
          → (b : cells (morphisms G j v x))
          → (c : cells (morphisms G j x y))
          → (d : cells (morphisms G j y z))
          → BiInvertibleCell j
                             (compHigher (com h) j u z)
                             k
                             (comp1 (com h) (comp1 (com h) a b) (comp1 (com h) c d))
                             (comp1 (com h) a (comp1 (com h) (comp1 (com h) b c) d))
origAssoc h {j} {k} {u} {v} {x} {y} {z} a b c d =
  comp1-2 h (invToBiInvCell k (assoc (hCat h) a b (comp1 (com h) c d)))
            (comp2' h
                    (id' (coin h j u v) k a)
                    (invToBiInvCell k (Inv.invIsInvCell k
                                                        (compHigher (com h) j v z)
                                                        (assoc (hCat h) b c d))))


generateBiComp i j k cA cB hC composition prevComp prevId f f' g g' .biComp bα bβ .f* =
  func (funcMorphisms composition k (f' , g') (f , g)) ((f* bα) , (f* bβ))
generateBiComp i j k cA cB hC composition prevComp prevId f f' g g' .biComp bα bβ .*f =
  func (funcMorphisms composition k (f' , g') (f , g)) ((*f bα) , (*f bβ))
generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB hC composition prevComp prevId f f' g g' .biComp {α} {β} bα bβ .fR l =
  comp1-3 h
          (comp1-3 h
                   (invToBiInvCell l (eq (compPreserve prevComp k l (f , g) (f' , g') (f , g)) l ((α , β) , f* bα , f* bβ)))
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

          (invToBiInvCell l (idPreserve prevId k l (f , g)))

generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB hC composition prevComp prevId f f' g g' .biComp {α} {β} bα bβ .fL l =
  comp1-3 h
          (comp1-3 h
                   (invToBiInvCell l (eq (compPreserve prevComp k l (f' , g') (f , g) (f' , g')) l ((*f bα , *f bβ) , α , β)))
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

          (invToBiInvCell l (idPreserve prevId k l (f' , g')))

generateBiComp i j k {A} {B} {C} {x} {x'} {y} {y'} {z} {z'} cA cB hC composition prevComp prevId f f' g g' .biCompHigher l =
  generateBiComp j
                 k
                 l
                 (compHigher cA j x x')
                 (compHigher cB j y y')
                 (coin hC j z z')
                 (funcMorphisms composition k (f , g) (f' , g'))
                 (compPreserveCoin prevComp k (f , g) (f' , g'))
                 (idPreserveCoin prevId k (f , g) (f' , g'))


compBiInv j h x y z .biComp bf bg .f* = comp1 (com h) (f* bg) (f* bf)
compBiInv j h x y z .biComp bf bg .*f = comp1 (com h) (*f bg) (*f bf)
compBiInv j h x y z .biComp {f} {g} bf bg .fR k =
  comp1-2 h (origAssoc h f g (f* bg) (f* bf))
            (comp1-2 h
                     (comp2' h
                             (id' (coin h j x y) k f)
                             (comp2' h
                                     (fR bg k)
                                     (id' (coin h j y x) k (f* bf))))
                     (comp1-2 h
                              (comp2' h
                                      (id' (coin h j x y) k f)
                                      (invToBiInvCell k (ƛ (hCat h) k (f* bf))))
                              (fR bf k)))
compBiInv j h x y z .biComp {f} {g} bf bg .fL k =
  comp1-2 h
          (origAssoc h (*f bg) (*f bf) f g)
          (comp1-2 h
                   (comp2' h
                           (id' (coin h j z y) k (*f bg))
                           (comp2' h
                                   (fL bf k)
                                   (id' (coin h j y z) k g)))
                   (comp1-2 h
                            (comp2' h
                                    (id' (coin h j z y) k (*f bg))
                                    (invToBiInvCell k (ƛ (hCat h) k g)))
                            (fL bg k)))

compBiInv {i = i} j h x y z .biCompHigher k f f' g g' =
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


leftBiInvIsInv : {a : Level}
               → {i : Size}
               → {G : GlobSet a i}
               → (j : Size< i)
               → (h : HigherCat i G)
               → {x y : cells G}
               → (f : cells (morphisms G j x y))
               → (bi : BiInvertible i (com h) j f)
               → BiInvertible i (com h) j (*f bi)
leftBiInvIsInv j h f bi .f* = f
leftBiInvIsInv j h f bi .*f = f
leftBiInvIsInv j h f bi .fR k = fL bi k
leftBiInvIsInv j h {x} {y} f bi .fL k =
  comp1-2 h
          (invToBiInvCell k (Inv.invIsInvCell k
                                              (compHigher (com h) j x x)
                                              (ρ (hCat h) k (comp1 (com h) f (*f bi)))))
          (comp1-2 h
                   (comp2' h
                           (comp2' h
                                   (id' (coin h j x y) k f)
                                   (id' (coin h j y x) k (*f bi)))
                           (record {
                             cell = *f (biInv (fR bi k)) ;
                             biInv = leftBiInvIsInv k (coin h j x x) (cell (fR bi k)) (biInv (fR bi k))
                           }))
                   (comp1-2 h
                            (origAssoc h f (*f bi) f (f* bi))
                            (comp1-2 h
                                     (comp2' h
                                             (id' (coin h j x y) k f)
                                             (comp2' h
                                                     (fL bi k)
                                                     (id' (coin h j y x) k (f* bi))))
                                     (comp1-2 h
                                              (comp2' h
                                                      (id' (coin h j x y) k f)
                                                      (invToBiInvCell k (ƛ (hCat h) k (f* bi))))
                                              (fR bi k)))))

rightBiInvIsInv : {a : Level}
                → {i : Size}
                → {G : GlobSet a i}
                → (j : Size< i)
                → (h : HigherCat i G)
                → {x y : cells G}
                → (f : cells (morphisms G j x y))
                → (bi : BiInvertible i (com h) j f)
                → BiInvertible i (com h) j (f* bi)
rightBiInvIsInv j h f bi .f* = f
rightBiInvIsInv j h f bi .*f = f
rightBiInvIsInv j h {x} {y} f bi .fR k =
  comp1-2 h
          (invToBiInvCell k (Inv.invIsInvCell k
                                              (compHigher (com h) j y y)
                                              (ƛ (hCat h) k (comp1 (com h) (f* bi) f))))
          (comp1-2 h
                   (comp2' h
                           (record {
                             cell = f* (biInv (fL bi k)) ;
                             biInv = rightBiInvIsInv k (coin h j y y) (cell (fL bi k)) (biInv (fL bi k))
                           })
                           (comp2' h
                                   (id' (coin h j y x) k (f* bi))
                                   (id' (coin h j x y) k f)))
                   (comp1-2 h
                            (origAssoc h (*f bi) f (f* bi) f)
                            (comp1-2 h
                                     (comp2' h
                                             (id' (coin h j y x) k (*f bi))
                                             (comp2' h
                                                     (fR bi k)
                                                     (id' (coin h j x y) k f)))
                                     (comp1-2 h
                                              (comp2' h
                                                      (id' (coin h j y x) k (*f bi))
                                                      (invToBiInvCell k (ƛ (hCat h) k f)))
                                              (fL bi k)))))

rightBiInvIsInv j h f bi .fL k = fR bi k
