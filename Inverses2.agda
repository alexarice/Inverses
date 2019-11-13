{-# OPTIONS --with-K --safe #-}

module Inverses2 where
open import Agda.Primitive
open import Data.Nat
open import Data.Product

record GlobSet : Set₁ where
  coinductive
  field
    cells : Set
    morphisms : cells → cells → GlobSet

open GlobSet

CompositionData : (G : GlobSet) → ℕ → Set
getFirst : (G : GlobSet) → (n : ℕ) → CompositionData G n → GlobSet
getSecond : (G : GlobSet) → (n : ℕ) → CompositionData G n → GlobSet

CompositionData G zero = cells G × cells G × cells G
CompositionData G (suc n) = Σ[ a ∈ CompositionData G n ] cells (getFirst G n a) × cells (getFirst G n a) × cells (getSecond G n a) × cells (getSecond G n a)
getFirst G zero (x , y , z) = morphisms G y z
getFirst G (suc n) (a , g , g' , f , f') = morphisms (getFirst G n a) g g'
getSecond G zero (x , y , z) = morphisms G x y
getSecond G (suc n) (a , g , g' , f , f') = morphisms (getSecond G n a) f f'

getResult : {n : ℕ} {G : GlobSet} → (prevres : CompositionData G n → GlobSet) → (lowerComp : (a : CompositionData G n) → cells (getFirst G n a) → cells (getSecond G n a) → cells (prevres a)) → CompositionData G (suc n) → GlobSet
getResult {n} {G} prevres lowerComp (a , g , g' , f , f') = morphisms (prevres a) (lowerComp a g f) (lowerComp a g' f')

record CompFunc {n : ℕ} {G : GlobSet} (prevres : CompositionData G n → GlobSet) (lowerComp : (a : CompositionData G n) → cells (getFirst G n a) → cells (getSecond G n a) → cells (prevres a)) : Set₁ where
  coinductive
  field
    comp' : (a : CompositionData G (suc n)) → cells (getFirst G (suc n) a) → cells (getSecond G (suc n) a) → cells (getResult prevres lowerComp a)
    next' : CompFunc {suc n} {G} (getResult prevres lowerComp) comp'

getZeroResult : (G : GlobSet) → CompositionData G zero → GlobSet
getZeroResult G (x , y , z) = morphisms G x z

p1 : {a : Level} {A B C : Set a} → A × B × C → A
p1 (x , y , z) = x

p2 : {a : Level} {A B C : Set a} → A × B × C → B
p2 (x , y , z) = y

p3 : {a : Level} {A B C : Set a} → A × B × C → C
p3 (x , y , z) = z

modifyComp : (G : GlobSet) → ((x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)) → (a : CompositionData G zero) → cells (morphisms G (p2 a) (p3 a)) → cells (morphisms G (p1 a) (p2 a)) → cells (morphisms G (p1 a) (p3 a))
modifyComp G oldComp (x , y , z) g f = oldComp x y z g f

record Composable (G : GlobSet) : Set₁ where
  coinductive
  field
    id : (x : cells G) → cells (morphisms G x x)
    comp : (x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)
    next : CompFunc {zero} {G} (getZeroResult G) (modifyComp G comp)
    {{coin}} : {x y : cells G} → Composable (morphisms G x y)

open Composable {{...}}

record BiInvertible {G : GlobSet} {{_ : Composable G}} {x y : cells G} (f : cells (morphisms G x y)) : Set₁ where
  coinductive
  field
    f* : cells (morphisms G y x)
    *f : cells (morphisms G y x)
    fR : cells (morphisms (morphisms G y y) (comp y x y f f*) (id y))
    fL : cells (morphisms (morphisms G x x) (comp x y x *f f) (id x))
    fRBiInv : BiInvertible {morphisms G y y} {{coin {G} {y} {y}}} fR
    fLBiInv : BiInvertible {morphisms G x x} {{coin {G} {x} {x}}} fL

record HCat (G : GlobSet) : Set₁ where
  field
    {{c}} : Composable G

idIsBiInv : {G : GlobSet} {{_ : HCat G}} → (x : cells G) → BiInvertible (id x)
BiInvertible.f* (idIsBiInv x) = id x
BiInvertible.*f (idIsBiInv x) = id x
BiInvertible.fR (idIsBiInv x) = {!!}
BiInvertible.fL (idIsBiInv x) = {!!}
BiInvertible.fRBiInv (idIsBiInv x) = {!!}
BiInvertible.fLBiInv (idIsBiInv x) = {!!}
