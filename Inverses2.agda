{-# OPTIONS --without-K --safe --guardedness #-}

module Inverses2 where
open import Agda.Primitive
open import Data.Nat
open import Data.Product
open import Agda.Builtin.Unit
open import Relation.Binary.PropositionalEquality.Core

record GlobSet : Set₁ where
  coinductive
  field
    cells : Set
    morphisms : cells → cells → GlobSet

open GlobSet

CompositionData : (G : GlobSet) → ℕ → Set
getUnderlyingFirst : (G : GlobSet) → (n : ℕ) → CompositionData G n → GlobSet
getFirst : (G : GlobSet) → (n : ℕ) → CompositionData G n → GlobSet
getUnderlyingSecond : (G : GlobSet) → (n : ℕ) → CompositionData G n → GlobSet
getSecond : (G : GlobSet) → (n : ℕ) → CompositionData G n → GlobSet

CompositionData G zero = cells G × cells G × cells G
CompositionData G (suc n) = Σ[ a ∈ CompositionData G n ] cells (getFirst G n a) × cells (getFirst G n a) × cells (getSecond G n a) × cells (getSecond G n a)

getUnderlyingFirst G zero a = G
getUnderlyingFirst G (suc n) (a , _) = getFirst G n a

getFirst G n a = morphisms (getUnderlyingFirst G n a) (c1 n a) (c2 n a)
 where
  c1 : (n : ℕ) → (a : CompositionData G n) → cells (getUnderlyingFirst G n a)
  c1 zero (x , y , z) = y
  c1 (suc n) (a , g , _) = g
  c2 : (n : ℕ) → (a : CompositionData G n) → cells (getUnderlyingFirst G n a)
  c2 zero (x , y , z) = z
  c2 (suc n) (a , g , g' , _ )= g'
getUnderlyingSecond G zero a = G
getUnderlyingSecond G (suc n) (a , _) = getSecond G n a

getSecond G n a = morphisms (getUnderlyingSecond G n a) (c1 n a) (c2 n a)
 where
  c1 : (n : ℕ) → (a : CompositionData G n) → cells (getUnderlyingSecond G n a)
  c1 zero (x , y , z) = x
  c1 (suc n) (a , g , g' , f , f') = f
  c2 : (n : ℕ) → (a : CompositionData G n) → cells (getUnderlyingSecond G n a)
  c2 zero (x , y , z) = y
  c2 (suc n) (a , g , g' , f , f') = f'

resultType : Set₁
resultType = Σ[ G ∈ GlobSet ] cells G × cells G

resultTypeToGlobSet : resultType → GlobSet
resultTypeToGlobSet (G , a , b) = morphisms G a b

getResult : {n : ℕ} {G : GlobSet} → (prevres : CompositionData G n → resultType) → (lowerComp : (a : CompositionData G n) → cells (getFirst G n a) → cells (getSecond G n a) → cells (resultTypeToGlobSet (prevres a))) → CompositionData G (suc n) → resultType
getResult {n} {G} prevres lowerComp (a , g , g' , f , f') = resultTypeToGlobSet (prevres a) , lowerComp a g f , lowerComp a g' f'

record CompFunc {n : ℕ} {G : GlobSet} (prevres : CompositionData G n → resultType) (lowerComp : (a : CompositionData G n) → cells (getFirst G n a) → cells (getSecond G n a) → cells (resultTypeToGlobSet (prevres a))) : Set₁ where
  coinductive
  field
    comp' : (a : CompositionData G (suc n)) → cells (getFirst G (suc n) a) → cells (getSecond G (suc n) a) → cells (resultTypeToGlobSet (getResult prevres lowerComp a))
    next' : CompFunc {suc n} {G} (getResult prevres lowerComp) comp'

open CompFunc

p1 : {a : Level} {A B C : Set a} → A × B × C → A
p1 (x , y , z) = x

p2 : {a : Level} {A B C : Set a} → A × B × C → B
p2 (x , y , z) = y

p3 : {a : Level} {A B C : Set a} → A × B × C → C
p3 (x , y , z) = z

modifyComp : (G : GlobSet) → ((x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)) → (a : CompositionData G zero) → cells (getFirst G zero a) → cells (getSecond G zero a) → cells (morphisms G (p1 a) (p3 a))
modifyComp G oldComp (x , y , z) g f = oldComp x y z g f

getZeroResult : (G : GlobSet) → CompositionData G zero → resultType
getZeroResult G (x , y , z) = G , x , z

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
compType G m = Σ[ r ∈ (CompositionData G m → (Σ[ g ∈ GlobSet ] cells g × cells g)) ] ((a : CompositionData G m) → cells (getFirst G m a) → cells (getSecond G m a) → cells (let (g , g1 , g2) = r a in morphisms g g1 g2))

comps : {n : ℕ} {G : GlobSet} → (prevres : CompositionData G n → resultType) → (lowerComp : (a : CompositionData G n) → cells (getFirst G n a) → cells (getSecond G n a) → cells (resultTypeToGlobSet (prevres a))) → (CompFunc {n} {G} prevres lowerComp) → IndexStream n (compType G)
head (comps prevres lowerComp cf) = prevres , lowerComp
tail (comps prevres lowerComp cf) = comps (getResult prevres lowerComp) (comp' cf) (next' cf)

getResultFromNat : {G : GlobSet} → (n : ℕ) → (c : (x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)) → CompFunc {zero} {G} (getZeroResult G) (modifyComp G c) → CompositionData G n → resultType
getResultFromNat {G} n c cf a = proj₁ (retrieve n (comps (getZeroResult G) (modifyComp G c) cf)) a

getCompFromNat : {G : GlobSet} → (n : ℕ) → (c : (x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)) → (cf : CompFunc {zero} {G} (getZeroResult G) (modifyComp G c)) → (a : CompositionData G n) → cells (getFirst G n a) → cells (getSecond G n a) → cells (resultTypeToGlobSet (getResultFromNat n c cf a))
getCompFromNat {G} n c cf a g f = proj₂ (retrieve n (comps (getZeroResult G) (modifyComp G c) cf)) a g f

record Composable (G : GlobSet) : Set₁ where
  coinductive
  field
    id : (x : cells G) → cells (morphisms G x x)
    comp : (x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)
    next : CompFunc {zero} {G} (getZeroResult G) (modifyComp G comp)
    coin : (x y : cells G) → Composable (morphisms G x y)
  resultn : (n : ℕ) → (a : CompositionData G n) → resultType
  resultn n = getResultFromNat n comp next
  compn : (n : ℕ) → (a : CompositionData G n) → cells (getFirst G n a) → cells (getSecond G n a) → cells (resultTypeToGlobSet (getResultFromNat n comp next a))
  compn n = getCompFromNat n comp next

open Composable {{...}}

underlyingFirstComp : (G : GlobSet) {{_ : Composable G}} → (n : ℕ) → (a : CompositionData G n) → Composable (getUnderlyingFirst G n a)
firstComp : (G : GlobSet) {{_ : Composable G}} (n : ℕ) → (a : CompositionData G n) → Composable (getFirst G n a)

underlyingFirstComp G {{cmp}} zero a = cmp
underlyingFirstComp G (suc n) (a , _) = firstComp G n a

firstComp G zero (x , y , z) = coin y z
firstComp G (suc n) a'@(a , g , g' , _) = Composable.coin (underlyingFirstComp G (suc n) a') g g'

underlyingSecondComp : (G : GlobSet) {{_ : Composable G}} → (n : ℕ) → (a : CompositionData G n) → Composable (getUnderlyingSecond G n a)
secondComp : (G : GlobSet) {{_ : Composable G}} → (n : ℕ) → (a : CompositionData G n) → Composable (getSecond G n a)

underlyingSecondComp G {{cmp}} zero a = cmp
underlyingSecondComp G (suc n) (a , _) = secondComp G n a

secondComp G zero (x , y , z) = coin x y
secondComp G (suc n) a'@(a , g , g' , f , f') = Composable.coin (underlyingSecondComp G (suc n) a') f f'

resultnComp : (G : GlobSet) {{_ : Composable G}} → (n : ℕ) → (a : CompositionData G n) → Composable (proj₁ (resultn n a))
resultnComp G n a = {!!}

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
    buildComp : (n : ℕ) → CompFunc {n} {terminal} (λ _ → terminal , tt , tt) (λ _ _ _ → tt)
    comp' (buildComp n) _ _ _ = tt
    next' (buildComp n) = buildComp (suc n)
Composable.coin compTerm tt tt = compTerm

equality : (A : Set) → GlobSet
cells (equality X) = X
morphisms (equality X) y z = equality (y ≡ z)

transport : {a : Level} {A B : Set a } → A ≡ B → A → B
transport refl x = x

myCong : {x y : GlobSet} {f f' : cells x} → (m : x ≡ y) → (F : (z : GlobSet) → cells z → cells z → GlobSet) → F x f f' ≡ F y (transport (cong cells m) f) (transport (cong cells m) f')
myCong refl F = refl

firstEqualityLem : (A : Set) → (n : ℕ) → (a : CompositionData (equality A) n) → (f f' : cells (getFirst (equality A) n a)) → morphisms (getFirst (equality A) n a) f f' ≡ equality (f ≡ f')
firstEqualityLem A zero a f f' = refl
firstEqualityLem A (suc n) (a , x , x' , y , y') f f' = helper (firstEqualityLem A n a x x')
  where
    helper2 : {A B : Set} {x y : A} → (p : A ≡ B) → (x ≡ y) ≡ (transport p x ≡ transport p y)
    helper2 refl = refl
    helper : morphisms (getFirst (equality A) n a) x x' ≡ equality (x ≡ x') → morphisms (getFirst (equality A) (suc n) (a , x , x' , y , y')) f f' ≡ equality (f ≡ f')
    helper m = let test = myCong m morphisms in trans test (cong equality (sym (helper2 (cong cells m))))

secondEqualityLem : (A : Set) → (n : ℕ) → (a : CompositionData (equality A) n) → (f f' : cells (getSecond (equality A) n a)) → morphisms (getSecond (equality A) n a) f f' ≡ equality (f ≡ f')
secondEqualityLem A zero a f f' = refl
secondEqualityLem A (suc n) (a , x , x' , y , y') f f' = helper (secondEqualityLem A n a y y')
  where
    helper2 : {A B : Set} {x y : A} → (p : A ≡ B) → (x ≡ y) ≡ (transport p x ≡ transport p y)
    helper2 refl = refl
    helper : morphisms (getSecond (equality A) n a) y y' ≡ equality (y ≡ y') → morphisms (getSecond (equality A) (suc n) (a , x , x' , y , y')) f f' ≡ equality (f ≡ f')
    helper m = let test = myCong m morphisms in trans test (cong equality (sym (helper2 (cong cells m))))

startComp : (A : Set) → (x y z : A) → y ≡ z → x ≡ y → x ≡ z
startComp _ _ _ _ refl refl = refl

compEq : (A : Set) → Composable (equality A)
Composable.id (compEq A) x = refl
Composable.comp (compEq A) = startComp A
Composable.next (compEq A) = buildComp zero (λ a → A , p1 a , p3 a) (modifyComp (equality A) (startComp A))
  where
    eqResultType : Set₁
    eqResultType = Σ[ S ∈ Set ] S × S
    eqResultTypeToResultType : eqResultType → resultType
    eqResultTypeToResultType (S , a , b) = (equality S , a , b)
    eqResultTypeToEquality : eqResultType → GlobSet
    eqResultTypeToEquality (S , a , b) = equality (a ≡ b)
    compHelper : (n : ℕ) → (prevres : CompositionData (equality A) n → eqResultType) (lowerComp : (a : CompositionData (equality A) n) → cells (getFirst (equality A) n a) → cells (getSecond (equality A) n a) → cells (eqResultTypeToEquality (prevres a))) → (a : CompositionData (equality A) (suc n)) → cells (getFirst (equality A) (suc n) a) → cells (getSecond (equality A) (suc n) a) → cells (resultTypeToGlobSet (getResult (λ a → eqResultTypeToResultType (prevres a)) lowerComp a))
    compHelper n prevres lowerComp (a , g , g' , f , f') α β = helper (transport (cong cells (firstEqualityLem A n a g g')) α) (transport (cong cells (secondEqualityLem A n a f f')) β) where
        helper : g ≡ g' → f ≡ f' → lowerComp a g f ≡ lowerComp a g' f'
        helper refl refl = refl
    buildComp : (n : ℕ) → (prevres : CompositionData (equality A) n → eqResultType) (lowerComp : (a : CompositionData (equality A) n) → cells (getFirst (equality A) n a) → cells (getSecond (equality A) n a) → cells (eqResultTypeToEquality (prevres a))) → CompFunc {n} {equality A} (λ a → eqResultTypeToResultType (prevres a)) lowerComp
    comp' (buildComp n prevres lowerComp) = compHelper n prevres lowerComp
    next' (buildComp n prevres lowerComp) = buildComp (suc n) (λ x → res x) (compHelper n prevres lowerComp)
      where
        res : CompositionData (equality A) (suc n) → eqResultType
        res (a , g , g' , f , f') = (proj₁ (proj₂ (prevres a)) ≡ proj₂ (proj₂ (prevres a))) , lowerComp a g f , lowerComp a g' f'

Composable.coin (compEq A) x y = compEq (x ≡ y)

idIsBiInv : {G : GlobSet} {{_ : Composable G}} {{_ : HCat G}} → (x : cells G) → BiInvertible (id x)
BiInvertible.f* (idIsBiInv x) = id x
BiInvertible.*f (idIsBiInv x) = id x
BiInvertible.fR (idIsBiInv x) = ƛ (id x)
BiInvertible.fL (idIsBiInv x) = ƛ (id x)
BiInvertible.fRBiInv (idIsBiInv x) = ƛBiInv (id x)
BiInvertible.fLBiInv (idIsBiInv x) = ƛBiInv (id x)

compIsBiInv : {G : GlobSet} {{_ : Composable G}} {{_ : HCat G}} {n : ℕ} → (a : CompositionData G n) → (g : cells (getFirst G n a)) → (f : cells (getSecond G n a)) → (BiInvertible {getUnderlyingFirst G n a} {{underlyingFirstComp G n a}} g) → (BiInvertible {getUnderlyingSecond G n a} {{underlyingSecondComp G n a}} f) → (BiInvertible {proj₁ (resultn n a)} {{resultnComp G n a}} (compn n a g f))
compIsBiInv = {!!}
