{-# OPTIONS --without-K --safe --sized-types #-}

module GlobSet.Product where
open import Data.Product public
open import GlobSet

infixr 2 _×G_

_×G_ : ∀ {i} → (G H : GlobSet i) → GlobSet i
cells (G ×G H) = cells G × cells H
morphisms (G ×G H) (w , x) (y , z) = morphisms G w y ×G morphisms H x z

infixr 3 _×GM_

_×GM_ : ∀ {i} {G H I J : GlobSet i} → GlobSetMorphism G H → GlobSetMorphism I J → GlobSetMorphism (G ×G I) (H ×G J)
func (ϕ ×GM ψ) (x , y) = (func ϕ x) , (func ψ y)
funcMorphisms (ϕ ×GM ψ) (x , y) (x' , y') = (funcMorphisms ϕ x x') ×GM funcMorphisms ψ y y'
