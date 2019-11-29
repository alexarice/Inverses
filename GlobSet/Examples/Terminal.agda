{-# OPTIONS --without-K --safe --sized-types #-}

module GlobSet.Examples.Terminal where
open import Agda.Builtin.Unit
open import GlobSet
open import GlobSet.Product
open import GlobSet.Composition

terminal : (i : Size) → GlobSet i
cells (terminal i)= ⊤
morphisms (terminal i) {j} _ _ = terminal j

compTerminal : ∀{i} → Composable (terminal i)
Composable.id compTerminal x = tt
Composable.comp compTerminal x y z = γ
 where
  γ : {j : Size} → GlobSetMorphism (terminal j ×G terminal j) (terminal j)
  func γ (f , g) = tt
  funcMorphisms γ (f , g) (f' , g') = γ
Composable.compHigher compTerminal x y = compTerminal
