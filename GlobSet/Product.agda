{-# OPTIONS --without-K --allow-unsolved-metas --sized-types #-}

module GlobSet.Product where
open import Data.Product public
open import GlobSet

infixr 2 _×G_

_×G_ : ∀{i} → (G H : GlobSet i) → GlobSet i
cells (G ×G H) = cells G × cells H
morphisms (G ×G H) (w , x) (y , z) = morphisms G w y ×G morphisms H x z

infixr 3 _×GM_

_×GM_ : ∀{i} {G H I J : GlobSet i} → GlobSetMorphism G H → GlobSetMorphism I J → GlobSetMorphism (G ×G I) (H ×G J)
func (ϕ ×GM ψ) (x , y) = (func ϕ x) , (func ψ y)
funcMorphisms (ϕ ×GM ψ) (x , y) (x' , y') = (funcMorphisms ϕ x x') ×GM funcMorphisms ψ y y'

prg₁ : ∀{i} (G H : GlobSet i) → GlobSetMorphism (G ×G H) G
func (prg₁ G H) (x , y) = x
funcMorphisms (prg₁ G H) (x , y) (x' , y') = prg₁ (morphisms G x x') (morphisms H y y')

prg₂ : ∀{i} (G H : GlobSet i) → GlobSetMorphism (G ×G H) H
func (prg₂ G H) (x , y) = y
funcMorphisms (prg₂ G H) (x , y) (x' , y') = prg₂ (morphisms G x x') (morphisms H y y')

symmetryG : ∀{i} (G H : GlobSet i) → GlobSetMorphism (G ×G H) (H ×G G)
func (symmetryG G H) (x , y) = y , x
funcMorphisms (symmetryG G H) (x , y) (x' , y') = symmetryG (morphisms G x x') (morphisms H y y')

interchangeG : ∀{i} (G H I J : GlobSet i) → GlobSetMorphism ((G ×G H) ×G (I ×G J)) ((G ×G I) ×G (H ×G J))
func (interchangeG G H I J) ((w , x) , (y , z)) = (w , y) , (x , z)
funcMorphisms (interchangeG G H I J) ((w , x) , (y , z)) ((w' , x') , (y' , z')) = interchangeG (morphisms G w w') (morphisms H x x') (morphisms I y y') (morphisms J z z')
