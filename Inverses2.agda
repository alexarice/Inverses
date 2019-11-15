{-# OPTIONS --with-K --safe --guardedness #-}

module Inverses2 where
open import Agda.Primitive
open import Data.Nat
open import Data.Product
open import Agda.Builtin.Unit

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

record CompFunc {n : ℕ} {G : GlobSet} (prevres' : CompositionData G n → GlobSet) (lowerComp' : (a : CompositionData G n) → cells (getFirst G n a) → cells (getSecond G n a) → cells (prevres' a)) : Set₁ where
  coinductive
  field
    comp' : (a : CompositionData G (suc n)) → cells (getFirst G (suc n) a) → cells (getSecond G (suc n) a) → cells (getResult prevres' lowerComp' a)
    next' : CompFunc {suc n} {G} (getResult prevres' lowerComp') comp'

open CompFunc



p1 : {a : Level} {A B C : Set a} → A × B × C → A
p1 (x , y , z) = x

p2 : {a : Level} {A B C : Set a} → A × B × C → B
p2 (x , y , z) = y

p3 : {a : Level} {A B C : Set a} → A × B × C → C
p3 (x , y , z) = z

modifyComp : (G : GlobSet) → ((x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)) → (a : CompositionData G zero) → cells (getFirst G zero a) → cells (getSecond G zero a) → cells (morphisms G (p1 a) (p3 a))
modifyComp G oldComp (x , y , z) g f = oldComp x y z g f

getZeroResult : (G : GlobSet) → CompositionData G zero → GlobSet
getZeroResult G (x , y , z) = morphisms G x z

record IndexStream {a : Level} (n : ℕ) (A : ℕ → Set a) : Set a where
  coinductive
  field
    head : A n
    tail : IndexStream (suc n) A

open IndexStream

retrieve : {a : Level} {A : ℕ → Set a} → (n : ℕ) → IndexStream zero A → A n
retrieve {_} {A} n i = head (helper n i)
  where
    helper : (m : ℕ) → IndexStream zero A → IndexStream m A
    helper zero i = i
    helper (suc m) i = tail (helper m i)

compType : (G : GlobSet) → ℕ → Set₁
compType G m = Σ[ r ∈ (CompositionData G m → GlobSet) ] ((a : CompositionData G m) → cells (getFirst G m a) → cells (getSecond G m a) → cells (r a))

comps : {n : ℕ} {G : GlobSet} → (prevres : CompositionData G n → GlobSet) → (lowerComp : (a : CompositionData G n) → cells (getFirst G n a) → cells (getSecond G n a) → cells (prevres a)) → (CompFunc {n} {G} prevres lowerComp) → IndexStream n (compType G)
head (comps prevres lowerComp cf) = prevres , lowerComp
tail (comps prevres lowerComp cf) = comps (getResult prevres lowerComp) (comp' cf) (next' cf)

getResultFromNat : {G : GlobSet} → (n : ℕ) → (c : (x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)) → CompFunc {zero} {G} (getZeroResult G) (modifyComp G c) → CompositionData G n → GlobSet
getResultFromNat {G} n c cf a = proj₁ (retrieve n (comps (getZeroResult G) (modifyComp G c) cf)) a

getCompFromNat : {G : GlobSet} → (n : ℕ) → (c : (x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)) → (cf : CompFunc {zero} {G} (getZeroResult G) (modifyComp G c)) → (a : CompositionData G n) → cells (getFirst G n a) → cells (getSecond G n a) → cells (getResultFromNat n c cf a)
getCompFromNat {G} n c cf a g f = proj₂ (retrieve n (comps (getZeroResult G) (modifyComp G c) cf)) a g f

record Composable (G : GlobSet) : Set₁ where
  coinductive
  field
    id : (x : cells G) → cells (morphisms G x x)
    comp : (x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)
    next : CompFunc {zero} {G} (getZeroResult G) (modifyComp G comp)
    coin : (x y : cells G) → Composable (morphisms G x y)
  compn : (n : ℕ) → (a : CompositionData G n) → cells (getFirst G n a) → cells (getSecond G n a) → cells (getResultFromNat n comp next a)
  compn n = getCompFromNat n comp next

open Composable {{...}}

record BiInvertible {G : GlobSet} {{_ : Composable G}} {x y : cells G} (f : cells (morphisms G x y)) : Set₁ where
  coinductive
  field
    f* : cells (morphisms G y x)
    *f : cells (morphisms G y x)
    fR : cells (morphisms (morphisms G y y) (comp y x y f f*) (id y))
    fL : cells (morphisms (morphisms G x x) (comp x y x *f f) (id x))
    fRBiInv : BiInvertible {morphisms G y y} {{coin y y}} fR
    fLBiInv : BiInvertible {morphisms G x x} {{coin x x}} fL

record HCat (G : GlobSet) {{_ : Composable G}} : Set₁ where
  coinductive
  field
    ƛ : {x y : cells G} → (f : cells (morphisms G x y)) → cells (morphisms (morphisms G x y) (comp x y y (id y) f) f)
    ƛBiInv : {x y : cells G} → (f : cells (morphisms G x y)) → BiInvertible {morphisms G x y} {{coin x y}} (ƛ f)
    hcoin : (x y : cells G) → HCat (morphisms G x y) {{coin x y}}

open HCat {{...}}

terminal : GlobSet
cells terminal = ⊤
morphisms terminal tt tt = terminal

compTerm : Composable terminal
Composable.id compTerm tt = tt
Composable.comp compTerm tt tt tt tt tt = tt
Composable.next compTerm = buildComp zero
  where
    buildComp : (n : ℕ) → CompFunc {n} {terminal} (λ _ → terminal) (λ _ _ _ → tt)
    comp' (buildComp n) _ _ _ = tt
    next' (buildComp n) = buildComp (suc n)
Composable.coin compTerm tt tt = compTerm



idIsBiInv : {G : GlobSet} {{_ : Composable G}} {{_ : HCat G}} → (x : cells G) → BiInvertible (id x)
BiInvertible.f* (idIsBiInv x) = id x
BiInvertible.*f (idIsBiInv x) = id x
BiInvertible.fR (idIsBiInv x) = ƛ (id x)
BiInvertible.fL (idIsBiInv x) = ƛ (id x)
BiInvertible.fRBiInv (idIsBiInv x) = ƛBiInv (id x)
BiInvertible.fLBiInv (idIsBiInv x) = ƛBiInv (id x)
