{-# OPTIONS --without-K --safe --sized-types #-}

module GlobSet.Product where
open import Data.Product public
open import GlobSet

infixr 2 _×G_

_×G_ : ∀{a b i} → (G : GlobSet a i) → (H : GlobSet b i) → GlobSet (a ⊔ b) i
cells (G ×G H) = cells G × cells H
morphisms (G ×G H) j (w , x) (y , z) = morphisms G j w y ×G morphisms H j x z

infixr 3 _×GM_

_×GM_ : {a b c d : Level}
      → {i : Size}
      → {G : GlobSet a i}
      → {H : GlobSet b i}
      → {I : GlobSet c i}
      → {J : GlobSet d i}
      → GlobSetMorphism G H
      → GlobSetMorphism I J
      → GlobSetMorphism (G ×G I) (H ×G J)
(ϕ ×GM ψ) .func (x , y) = (func ϕ x) , (func ψ y)
(ϕ ×GM ψ) .funcMorphisms j (x , y) (x' , y') = (funcMorphisms ϕ j x x') ×GM funcMorphisms ψ j y y'

prg₁ : {a b : Level}
     → {i : Size}
     → (G : GlobSet a i)
     → (H : GlobSet b i)
     → GlobSetMorphism (G ×G H) G
prg₁ G H .func (x , y) = x
prg₁ G H .funcMorphisms j (x , y) (x' , y') = prg₁ (morphisms G j x x') (morphisms H j y y')

prg₂ : {a b : Level}
     → {i : Size}
     → (G : GlobSet a i)
     → (H : GlobSet b i)
     → GlobSetMorphism (G ×G H) H
prg₂ G H .func (x , y) = y
prg₂ G H .funcMorphisms j (x , y) (x' , y') = prg₂ (morphisms G j x x') (morphisms H j y y')

symmetryG : {a b : Level}
          → {i : Size}
          → (G : GlobSet a i)
          → (H : GlobSet b i)
          → GlobSetMorphism (G ×G H) (H ×G G)
symmetryG G H .func (x , y) = y , x
symmetryG G H .funcMorphisms j (x , y) (x' , y') = symmetryG (morphisms G j x x') (morphisms H j y y')

interchangeG : {a b c d : Level}
             → {i : Size}
             → (G : GlobSet a i)
             → (H : GlobSet b i)
             → (I : GlobSet c i)
             → (J : GlobSet d i)
             → GlobSetMorphism ((G ×G H) ×G (I ×G J)) ((G ×G I) ×G (H ×G J))
interchangeG G H I J .func ((w , x) , (y , z)) = (w , y) , (x , z)
interchangeG G H I J .funcMorphisms j ((w , x) , (y , z)) ((w' , x') , (y' , z')) =
  interchangeG (morphisms G j w w')
               (morphisms H j x x')
               (morphisms I j y y')
               (morphisms J j z z')
