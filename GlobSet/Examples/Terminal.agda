{-# OPTIONS --safe --without-K --sized-types #-}

module GlobSet.Examples.Terminal where
open import Agda.Builtin.Unit
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.BiInvertible
open import GlobSet.HCat

terminal : (i : Size) → GlobSet i
cells (terminal i)= ⊤
morphisms (terminal i) j _ _ = terminal j

terminalCompHelper : (j : Size) → GlobSetMorphism (terminal j ×G terminal j) (terminal j)
func (terminalCompHelper j) (f , g) = tt
funcMorphisms (terminalCompHelper j) k (f , g) (f' , g') = terminalCompHelper k

compTerminal : (i : Size) → Composable i (terminal i)
Composable.id (compTerminal i) j x = tt
Composable.comp (compTerminal i) j x y z = terminalCompHelper j
Composable.compHigher (compTerminal i) j x y = (compTerminal j)

terminalInvertibleMorphisms : (i : Size)
                              (j : Size< i)
                            → BiInvertible i (compTerminal i) j tt
f* (terminalInvertibleMorphisms i j) = tt
*f (terminalInvertibleMorphisms i j) = tt
fR (terminalInvertibleMorphisms i j) k = tt
fL (terminalInvertibleMorphisms i j) k = tt
fRBiInv (terminalInvertibleMorphisms i j) k = terminalInvertibleMorphisms j k
fLBiInv (terminalInvertibleMorphisms i j) k = terminalInvertibleMorphisms j k

hCatTerminal : (i : Size) → HCat (terminal i) (compTerminal i)
compPreserveId (hCatTerminal i) j x y z = γ i j
 where
  γ : (i : Size)
    → (j : Size< i)
    → PreserveIden (prodComp (compTerminal j)
                             (compTerminal j))
                   (compTerminal j)
                   (terminalCompHelper j)
  idPreserve (γ i j) k l w = tt
  idPreserveBiInv (γ i j) k l w = terminalInvertibleMorphisms k l
  idPreserveCoin (γ i j) k w₁ w₂ = γ j k
compPreserveComp (hCatTerminal i) j x y z = γ i j
 where
  γ : (i : Size)
    → (j : Size< i)
    → PreserveComp (prodComp (compTerminal j)
                             (compTerminal j))
                   (compTerminal j)
                   (terminalCompHelper j)
  eq (compPreserve (γ i j) k l x y z) m w = tt
  eqBiInv (compPreserve (γ i j) k l x y z) m w = terminalInvertibleMorphisms k m
  compPreserveCoin (γ i j) k x y = γ j k
ƛ (hCatTerminal i) k f = tt
ƛBiInv (hCatTerminal i) {j} k f = terminalInvertibleMorphisms j k
assoc (hCatTerminal i) a b c d = tt
assocBiInv (hCatTerminal i) {j} {k} a b c d = terminalInvertibleMorphisms j k
hcoin (hCatTerminal i) j x y = hCatTerminal j
