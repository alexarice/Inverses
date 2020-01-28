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
idIsInv j h x .finv = id (com h) j x
idIsInv j h x .fR k = ƛ (hCat h) k (id (com h) j x)
idIsInv j h x .fL k = ƛ (hCat h) k (id (com h) j x)

id' : {a : Level}
    → {i : Size}
    → (j : Size< i)
    → {G : GlobSet a i}
    → (h : HigherCat i G)
    → (x : cells G)
    → InvertibleCell i (com h) j x x
id' j h x .cell = id (com h) j x
id' j h x .invert = idIsInv j h x

invIsInv : {a : Level}
         → {i : Size}
         → (j : Size< i)
         → {G : GlobSet a i}
         → (c : Composable i G)
         → {x y : cells G}
         → (f : cells (morphisms G j x y))
         → (inv : Invertible i c j f)
         → Invertible i c j (finv inv)
invIsInv j c f inv .finv = f
invIsInv j c f inv .fR k = fL inv k
invIsInv j c f inv .fL k = fR inv k

invIsInvCell : {a : Level}
             → {i : Size}
             → (j : Size< i)
             → {G : GlobSet a i}
             → (c : Composable i G)
             → {x y : cells G}
             → (inv : InvertibleCell i c j x y)
             → InvertibleCell i c j y x
invIsInvCell j c inv .cell = finv (invert inv)
invIsInvCell j c inv .invert = invIsInv j c (cell inv) (invert inv)
