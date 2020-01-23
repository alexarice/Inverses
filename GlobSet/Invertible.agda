{-# OPTIONS --sized-types --safe --without-K #-}

module GlobSet.Invertible where

open import GlobSet.Invertible.Core public
open import GlobSet
open import GlobSet.Composition
open import GlobSet.HCat

idIsInv : {a : Level}
        → {i : Size}
        → (j : Size< i)
        → {G : GlobSet a i}
        → (h : HigherCat i G)
        → (x : cells G)
        → Invertible i (com h) j (id (com h) j x)
finv (idIsInv j h x) = id (com h) j x
fR (idIsInv j h x) k = ƛ (hCat h) k (id (com h) j x)
fL (idIsInv j h x) k = ƛ (hCat h) k (id (com h) j x)

id' : {a : Level}
    → {i : Size}
    → (j : Size< i)
    → {G : GlobSet a i}
    → (h : HigherCat i G)
    → (x : cells G)
    → InvertibleCell i (com h) j x x
cell (id' j h x) = id (com h) j x
invert (id' j h x) = idIsInv j h x

invIsInv : {a : Level}
         → {i : Size}
         → (j : Size< i)
         → {G : GlobSet a i}
         → (c : Composable i G)
         → {x y : cells G}
         → (f : cells (morphisms G j x y))
         → (inv : Invertible i c j f)
         → Invertible i c j (finv inv)
finv (invIsInv j c f inv) = f
fR (invIsInv j c f inv) k = fL inv k
fL (invIsInv j c f inv) k = fR inv k

invIsInvCell : {a : Level}
             → {i : Size}
             → (j : Size< i)
             → {G : GlobSet a i}
             → (c : Composable i G)
             → {x y : cells G}
             → (inv : InvertibleCell i c j x y)
             → InvertibleCell i c j y x
cell (invIsInvCell j c inv) = finv (invert inv)
invert (invIsInvCell j c inv) = invIsInv j c (cell inv) (invert inv)
