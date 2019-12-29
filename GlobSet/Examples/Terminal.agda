{-# OPTIONS --without-K --sized-types #-}

module GlobSet.Examples.Terminal where
open import Agda.Builtin.Unit
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition

terminal : (i : Size) → GlobSet i
cells (terminal i)= ⊤
morphisms (terminal i) j _ _ = terminal j

compTerminal : {i : Size} → Composable i (terminal i)
Composable.id compTerminal j x = tt
Composable.comp compTerminal j x y z = γ
 where
  γ : {j : Size} → GlobSetMorphism (terminal j ×G terminal j) (terminal j)
  func γ (f , g) = tt
  funcMorphisms γ j (f , g) (f' , g') = γ
Composable.compHigher compTerminal j x y = compTerminal
