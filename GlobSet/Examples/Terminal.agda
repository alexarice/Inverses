{-# OPTIONS --safe --without-K --sized-types #-}

module GlobSet.Examples.Terminal where
open import Agda.Builtin.Unit
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.Invertible
open import GlobSet.HCat

terminal : (i : Size) → GlobSet 0ℓ i
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
                            → InvertibleCell i (compTerminal i) j tt tt
cell (terminalInvertibleMorphisms i j) = tt
finv (invert (terminalInvertibleMorphisms i j)) = tt
fR (invert (terminalInvertibleMorphisms i j)) = terminalInvertibleMorphisms j
fL (invert (terminalInvertibleMorphisms i j)) = terminalInvertibleMorphisms j

hCatTerminal : (i : Size) → HCat (terminal i) (compTerminal i)
compPreserveId (hCatTerminal i) j x y z = γ i j
 where
  γ : (i : Size)
    → (j : Size< i)
    → PreserveIden (prodComp (compTerminal j)
                             (compTerminal j))
                   (compTerminal j)
                   (terminalCompHelper j)
  idPreserve (γ i j) k l w = terminalInvertibleMorphisms k l
  idPreserveCoin (γ i j) k w₁ w₂ = γ j k
compPreserveComp (hCatTerminal i) j x y z = γ i j
 where
  γ : (i : Size)
    → (j : Size< i)
    → PreserveComp (prodComp (compTerminal j)
                             (compTerminal j))
                   (compTerminal j)
                   (terminalCompHelper j)
  eq (compPreserve (γ i j) k l x y z) m w = terminalInvertibleMorphisms k m
  compPreserveCoin (γ i j) k x y = γ j k
ƛ (hCatTerminal i) {j} k f = terminalInvertibleMorphisms j k
assoc (hCatTerminal i) {j} {k} a b c = terminalInvertibleMorphisms j k
hcoin (hCatTerminal i) j x y = hCatTerminal j
