{-# OPTIONS --safe --without-K --sized-types #-}

module GlobSet.Examples.Terminal where
open import Agda.Builtin.Unit
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition
open import GlobSet.Invertible
open import GlobSet.HCat

terminal : (i : Size) → GlobSet 0ℓ i
terminal i .cells = ⊤
terminal i .morphisms j _ _ = terminal j

terminalCompHelper : (j : Size) → GlobSetMorphism (terminal j ×G terminal j) (terminal j)
terminalCompHelper j .func (f , g) = tt
terminalCompHelper j .funcMorphisms k (f , g) (f' , g') = terminalCompHelper k

compTerminal : (i : Size) → Composable i (terminal i)
compTerminal i .id j x = tt
compTerminal i .comp j x y z = terminalCompHelper j
compTerminal i .compHigher j x y = (compTerminal j)

terminalInvertibleMorphisms : (i : Size)
                              (j : Size< i)
                            → InvertibleCell i (compTerminal i) j tt tt
terminalInvertibleMorphisms i j .cell = tt
terminalInvertibleMorphisms i j .invert .finv = tt
terminalInvertibleMorphisms i j .invert .fR = terminalInvertibleMorphisms j
terminalInvertibleMorphisms i j .invert .fL = terminalInvertibleMorphisms j

hCatTerminal : (i : Size) → HCat (terminal i) (compTerminal i)
hCatTerminal i .compPreserveId j x y z = γ i j
 where
  γ : (i : Size)
    → (j : Size< i)
    → PreserveIden (prodComp (compTerminal j)
                             (compTerminal j))
                   (compTerminal j)
                   (terminalCompHelper j)
  γ i j .idPreserve k l w = terminalInvertibleMorphisms k l
  γ i j .idPreserveCoin k w₁ w₂ = γ j k
hCatTerminal i .compPreserveComp j x y z = γ i j
 where
  γ : (i : Size)
    → (j : Size< i)
    → PreserveComp (prodComp (compTerminal j)
                             (compTerminal j))
                   (compTerminal j)
                   (terminalCompHelper j)
  γ i j .compPreserve k l x y z .eq m w = terminalInvertibleMorphisms k m
  γ i j .compPreserveCoin k x y = γ j k
hCatTerminal i .ƛ {j} k f = terminalInvertibleMorphisms j k
hCatTerminal i .ρ {j} k f = terminalInvertibleMorphisms j k
hCatTerminal i .assoc {j} {k} a b c = terminalInvertibleMorphisms j k
hCatTerminal i .hcoin j x y = hCatTerminal j
