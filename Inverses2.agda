{-# OPTIONS --without-K --safe --guardedness #-}

module Inverses2 where
open import Agda.Primitive
open import Data.Nat
open import Data.Product
open import Agda.Builtin.Unit
open import Relation.Binary.PropositionalEquality.Core

transport : {a : Level} {A B : Set a} → A ≡ B → A → B
transport refl a = a

record GlobSet : Set₁ where
  coinductive
  field
    cells : Set
    morphisms : cells → cells → GlobSet

open GlobSet

data Descendant (G : GlobSet) : ℕ → Set

realise : (G : GlobSet) → (n : ℕ) → Descendant G n → GlobSet

data Descendant G where
  Orig : Descendant G zero
  Child : {n : ℕ} (d : Descendant G n) → (x y : cells (realise G n d)) → Descendant G (suc n)

realise G zero Orig = G
realise G (suc n) (Child d x y) = morphisms (realise G n d) x y

pushToDesc : {a : Level} {G : GlobSet} (F : GlobSet → Set a) → ({G' : GlobSet} → F G' → (x y : cells G') → F (morphisms G' x y)) → {n : ℕ} (d : Descendant G n) → F G → F (realise G n d)
pushToDesc F ind Orig base = base
pushToDesc F ind (Child d x y) base = ind (pushToDesc F ind d base) x y

CompositionData : (G : GlobSet) → ℕ → Set
getUnderlyingFirstDescendant : (G : GlobSet) → (n : ℕ) → CompositionData G n → Descendant G n
getFirstDescendant : (G : GlobSet) → (n : ℕ) → CompositionData G n → Descendant G (suc n)
getUnderlyingSecondDescendant : (G : GlobSet) → (n : ℕ) → CompositionData G n → Descendant G n
getSecondDescendant : (G : GlobSet) → (n : ℕ) → CompositionData G n → Descendant G (suc n)
getUnderlyingFirst : (G : GlobSet) → (n : ℕ) → CompositionData G n → Set
getFirst : (G : GlobSet) → (n : ℕ) → CompositionData G n → Set
getUnderlyingSecond : (G : GlobSet) → (n : ℕ) → CompositionData G n → Set
getSecond : (G : GlobSet) → (n : ℕ) → CompositionData G n → Set

getUnderlyingFirst G n a = cells (realise G n (getUnderlyingFirstDescendant G n a))
getFirst G n a = cells (realise G (suc n) (getFirstDescendant G n a))
getUnderlyingSecond G n a = cells (realise G n (getUnderlyingSecondDescendant G n a))
getSecond G n a = cells (realise G (suc n) (getSecondDescendant G n a))

CompositionData G zero = cells G × cells G × cells G
CompositionData G (suc n) = Σ[ a ∈ CompositionData G n ] getFirst G n a × getFirst G n a × getSecond G n a × getSecond G n a

getUnderlyingFirstDescendant G zero a = Orig
getUnderlyingFirstDescendant G (suc n) (a , _) = getFirstDescendant G n a

getFirstDescendant G n a = Child (getUnderlyingFirstDescendant G n a) (c1 n a) (c2 n a)
 where
  c1 : (n : ℕ) → (a : CompositionData G n) → getUnderlyingFirst G n a
  c1 zero (x , y , z) = y
  c1 (suc n) (a , g , _) = g
  c2 : (n : ℕ) → (a : CompositionData G n) → getUnderlyingFirst G n a
  c2 zero (x , y , z) = z
  c2 (suc n) (a , g , g' , _ ) = g'

getUnderlyingSecondDescendant G zero a = Orig
getUnderlyingSecondDescendant G (suc n) (a , _) = getSecondDescendant G n a

getSecondDescendant G n a = Child (getUnderlyingSecondDescendant G n a) (c1 n a) (c2 n a)
 where
  c1 : (n : ℕ) → (a : CompositionData G n) → getUnderlyingSecond G n a
  c1 zero (x , y , z) = x
  c1 (suc n) (a , g , g' , f , f') = f
  c2 : (n : ℕ) → (a : CompositionData G n) → getUnderlyingSecond G n a
  c2 zero (x , y , z) = y
  c2 (suc n) (a , g , g' , f , f') = f'

resultType : GlobSet → ℕ → Set
resultType G n = Σ[ d ∈ Descendant G n ] cells (realise G n d) × cells (realise G n d)

resultTypeToDescendant : {G : GlobSet} {n : ℕ} → resultType G n → Descendant G (suc n)
resultTypeToDescendant (d , a , b) = Child d a b

resultTypeToSet : {G : GlobSet} {n : ℕ} → resultType G n → Set
resultTypeToSet {G} {n} r = cells (realise G (suc n) (resultTypeToDescendant r))

getResult : {n : ℕ} {G : GlobSet} → (prevres : CompositionData G n → resultType G n) → (lowerComp : (a : CompositionData G n) → getFirst G n a → getSecond G n a → resultTypeToSet (prevres a)) → CompositionData G (suc n) → resultType G (suc n)
getResult {n} {G} prevres lowerComp (a , g , g' , f , f') = resultTypeToDescendant (prevres a) , lowerComp a g f , lowerComp a g' f'

record CompFunc {n : ℕ} {G : GlobSet} (prevres : CompositionData G n → resultType G n) (lowerComp : (a : CompositionData G n) → getFirst G n a → getSecond G n a → resultTypeToSet (prevres a)) : Set₁ where
  coinductive
  field
    comp' : (a : CompositionData G (suc n)) → getFirst G (suc n) a → getSecond G (suc n) a → resultTypeToSet (getResult prevres lowerComp a)
    next' : CompFunc {suc n} {G} (getResult prevres lowerComp) comp'

open CompFunc

p1 : {a : Level} {A B C : Set a} → A × B × C → A
p1 (x , y , z) = x

p2 : {a : Level} {A B C : Set a} → A × B × C → B
p2 (x , y , z) = y

p3 : {a : Level} {A B C : Set a} → A × B × C → C
p3 (x , y , z) = z

modifyComp : (G : GlobSet) → ((x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)) → (a : CompositionData G zero) → getFirst G zero a → getSecond G zero a → cells (morphisms G (p1 a) (p3 a))
modifyComp G oldComp (x , y , z) g f = oldComp x y z g f

getZeroResult : (G : GlobSet) → CompositionData G zero → resultType G zero
getZeroResult G (x , y , z) = Orig , x , z

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

compType : (G : GlobSet) → ℕ → Set
compType G m = Σ[ r ∈ (CompositionData G m → resultType G m) ] ((a : CompositionData G m) → getFirst G m a → getSecond G m a → resultTypeToSet (r a))

comps : {n : ℕ} {G : GlobSet} → (prevres : CompositionData G n → resultType G n) → (lowerComp : (a : CompositionData G n) → getFirst G n a → getSecond G n a → resultTypeToSet (prevres a)) → (CompFunc {n} {G} prevres lowerComp) → IndexStream n (compType G)
head (comps prevres lowerComp cf) = prevres , lowerComp
tail (comps prevres lowerComp cf) = comps (getResult prevres lowerComp) (comp' cf) (next' cf)

getResultFromNat : {G : GlobSet} → (n : ℕ) → (c : (x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)) → CompFunc {zero} {G} (getZeroResult G) (modifyComp G c) → CompositionData G n → resultType G n
getResultFromNat {G} n c cf a = proj₁ (retrieve n (comps (getZeroResult G) (modifyComp G c) cf)) a

getCompFromNat : {G : GlobSet} → (n : ℕ) → (c : (x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)) → (cf : CompFunc {zero} {G} (getZeroResult G) (modifyComp G c)) → (a : CompositionData G n) → getFirst G n a → getSecond G n a → resultTypeToSet (getResultFromNat n c cf a)
getCompFromNat {G} n c cf a g f = proj₂ (retrieve n (comps (getZeroResult G) (modifyComp G c) cf)) a g f

record Composable (G : GlobSet) : Set₁ where
  coinductive
  field
    id : (x : cells G) → cells (morphisms G x x)
    comp : (x y z : cells G) → cells (morphisms G y z) → cells (morphisms G x y) → cells (morphisms G x z)
    next : CompFunc {zero} {G} (getZeroResult G) (modifyComp G comp)
    coin : (x y : cells G) → Composable (morphisms G x y)
  resultn : (n : ℕ) → (a : CompositionData G n) → resultType G n
  resultn n = getResultFromNat n comp next
  compn : (n : ℕ) → (a : CompositionData G n) → getFirst G n a → getSecond G n a → resultTypeToSet (getResultFromNat n comp next a)
  compn n = getCompFromNat n comp next

open Composable {{...}}

underlyingFirstComp : (G : GlobSet) {{_ : Composable G}} → (n : ℕ) → (a : CompositionData G n) → Composable (realise G n (getUnderlyingFirstDescendant G n a))
firstComp : (G : GlobSet) {{_ : Composable G}} (n : ℕ) → (a : CompositionData G n) → Composable (realise G (suc n) (getFirstDescendant G n a))

underlyingFirstComp G {{cmp}} zero a = cmp
underlyingFirstComp G (suc n) (a , _) = firstComp G n a

firstComp G zero (x , y , z) = coin y z
firstComp G (suc n) a'@(a , g , g' , _) = Composable.coin (underlyingFirstComp G (suc n) a') g g'

underlyingSecondComp : (G : GlobSet) {{_ : Composable G}} → (n : ℕ) → (a : CompositionData G n) → Composable (realise G n (getUnderlyingSecondDescendant G n a))
secondComp : (G : GlobSet) {{_ : Composable G}} → (n : ℕ) → (a : CompositionData G n) → Composable (realise G (suc n) (getSecondDescendant G n a))

underlyingSecondComp G {{cmp}} zero a = cmp
underlyingSecondComp G (suc n) (a , _) = secondComp G n a

secondComp G zero (x , y , z) = coin x y
secondComp G (suc n) a'@(a , g , g' , f , f') = Composable.coin (underlyingSecondComp G (suc n) a') f f'

record BiInvertible {G : GlobSet} {{_ : Composable G}} {x y : cells G} (f : cells (morphisms G x y)) : Set₁ where
  coinductive
  field
    f* : cells (morphisms G y x)
    *f : cells (morphisms G y x)
    fR : cells (morphisms (morphisms G y y) (comp y x y f f*) (id y))
    fL : cells (morphisms (morphisms G x x) (comp x y x *f f) (id x))
    fRBiInv : BiInvertible {morphisms G y y} {{coin y y}} fR
    fLBiInv : BiInvertible {morphisms G x x} {{coin x x}} fL

open BiInvertible

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
    buildDesc : (n : ℕ) → Descendant terminal n
    lemMorphTerm : {X : GlobSet} → terminal ≡ X → {x y : cells X} → terminal ≡ morphisms X x y
    lemMorphTerm refl = refl
    termDescIsTerm : {n : ℕ} → (d : Descendant terminal n) → terminal ≡ realise terminal n d
    termDescIsTerm {zero} Orig = refl
    termDescIsTerm {suc n} (Child d x y) = lemMorphTerm (termDescIsTerm d)
    ttToDesc : {n : ℕ} → (d : Descendant terminal n) → cells (realise terminal n d)
    ttToDesc d = transport (cong cells (termDescIsTerm d)) tt
    buildDesc zero = Orig
    buildDesc (suc n) = Child (buildDesc n) (ttToDesc (buildDesc n)) (ttToDesc (buildDesc n))
    buildComp : (n : ℕ) → CompFunc {n} {terminal} (λ _ → buildDesc n , ttToDesc (buildDesc n) , ttToDesc (buildDesc n)) λ _ _ _ → transport (cong cells (lemMorphTerm (termDescIsTerm (buildDesc n)))) tt
    comp' (buildComp n) _ _ _ = transport (cong cells (lemMorphTerm (lemMorphTerm (termDescIsTerm (buildDesc n))))) tt
    next' (buildComp n) = buildComp (suc n)
Composable.coin compTerm tt tt = compTerm

equality : (A : Set) → GlobSet
cells (equality X) = X
morphisms (equality X) y z = equality (y ≡ z)

myCong : {x y : GlobSet} {f f' : cells x} → (m : x ≡ y) → (F : (z : GlobSet) → cells z → cells z → GlobSet) → F x f f' ≡ F y (transport (cong cells m) f) (transport (cong cells m) f')
myCong refl F = refl

firstEqualityLem : (A : Set) → (n : ℕ) → (a : CompositionData (equality A) n) → (f f' : getFirst (equality A) n a) → morphisms (realise (equality A) (suc n) (getFirstDescendant (equality A) n a)) f f' ≡ equality (f ≡ f')
firstEqualityLem A zero a f f' = refl
firstEqualityLem A (suc n) (a , x , x' , y , y') f f' = helper (firstEqualityLem A n a x x')
  where
    helper2 : {A B : Set} {x y : A} → (p : A ≡ B) → (x ≡ y) ≡ (transport p x ≡ transport p y)
    helper2 refl = refl
    helper : morphisms (realise (equality A) (suc n) (getFirstDescendant (equality A) n a)) x x' ≡ equality (x ≡ x') → morphisms (realise (equality A) (suc (suc n)) (getFirstDescendant (equality A) (suc n) (a , x , x' , y , y'))) f f' ≡ equality (f ≡ f')
    helper m = let test = myCong m morphisms in trans test (cong equality (sym (helper2 (cong cells m))))

secondEqualityLem : (A : Set) → (n : ℕ) → (a : CompositionData (equality A) n) → (f f' : getSecond (equality A) n a) → morphisms (realise (equality A) (suc n) (getSecondDescendant (equality A) n a)) f f' ≡ equality (f ≡ f')
secondEqualityLem A zero a f f' = refl
secondEqualityLem A (suc n) (a , x , x' , y , y') f f' = helper (secondEqualityLem A n a y y')
  where
    helper2 : {A B : Set} {x y : A} → (p : A ≡ B) → (x ≡ y) ≡ (transport p x ≡ transport p y)
    helper2 refl = refl
    helper : morphisms (realise (equality A) (suc n) (getSecondDescendant (equality A) n a)) y y' ≡ equality (y ≡ y') → morphisms (realise (equality A) (suc (suc n)) (getSecondDescendant (equality A) (suc n) (a , x , x' , y , y'))) f f' ≡ equality (f ≡ f')
    helper m = let test = myCong m morphisms in trans test (cong equality (sym (helper2 (cong cells m))))

startComp : (A : Set) → (x y z : A) → y ≡ z → x ≡ y → x ≡ z
startComp _ _ _ _ refl refl = refl

compEq : (A : Set) → Composable (equality A)
Composable.id (compEq A) x = refl
Composable.comp (compEq A) = startComp A
Composable.next (compEq A) = buildComp zero (λ a → Orig , p1 a , p3 a) (modifyComp (equality A) (startComp A))
  where
    compHelper : (n : ℕ) → (prevres : CompositionData (equality A) n → resultType (equality A) n) (lowerComp : (a : CompositionData (equality A) n) → getFirst (equality A) n a → getSecond (equality A) n a → resultTypeToSet (prevres a)) → (a : CompositionData (equality A) (suc n)) → getFirst (equality A) (suc n) a → getSecond (equality A) (suc n) a → resultTypeToSet (getResult prevres lowerComp a)
    compHelper n prevres lowerComp (a , g , g' , f , f') α β = {!!}
     where
      helper : g ≡ g' → f ≡ f' → lowerComp a g f ≡ lowerComp a g' f'
      helper refl refl = refl
      innerEq : lowerComp a g f ≡ lowerComp a g' f'
      innerEq = helper (transport (cong cells (firstEqualityLem A n a g g')) α) (transport (cong cells (secondEqualityLem A n a f f')) β)
    buildComp : (n : ℕ) → (prevres : CompositionData (equality A) n → resultType (equality A) n) (lowerComp : (a : CompositionData (equality A) n) → getFirst (equality A) n a → getSecond (equality A) n a → resultTypeToSet (prevres a)) → CompFunc {n} {equality A} prevres lowerComp
    comp' (buildComp n prevres lowerComp) = transport {!!} (compHelper n prevres lowerComp)
    next' (buildComp n prevres lowerComp) = buildComp (suc n) (λ a → getResult prevres lowerComp a) (compHelper n prevres lowerComp)


Composable.coin (compEq A) x y = compEq (x ≡ y)

idIsBiInv : {G : GlobSet} {{_ : Composable G}} {{_ : HCat G}} → (x : cells G) → BiInvertible (id x)
f* (idIsBiInv x) = id x
*f (idIsBiInv x) = id x
fR (idIsBiInv x) = ƛ (id x)
fL (idIsBiInv x) = ƛ (id x)
fRBiInv (idIsBiInv x) = ƛBiInv (id x)
fLBiInv (idIsBiInv x) = ƛBiInv (id x)

compIsBiInv : {G : GlobSet} {{c : Composable G}} {{_ : HCat G}} → (n : ℕ) → (a : CompositionData G n) → (g : getFirst G n a) → (f : getSecond G n a) → (BiInvertible {realise G n (getUnderlyingFirstDescendant G n a)} {{underlyingFirstComp G n a}} g) → (BiInvertible {realise G n (getUnderlyingSecondDescendant G n a)} {{underlyingSecondComp G n a}} f) → (BiInvertible {realise G n (proj₁ (resultn n a))} {{pushToDesc Composable Composable.coin (proj₁ (resultn n a)) c}} (compn n a g f))
compIsBiInv zero a g f bf bg = {!!}
f* (compIsBiInv (suc zero) ((x , y , z) , g , g' , f , f') α β bα bβ) = compn (suc zero) (((x , y , z) , g' , g , f' , f)) (f* {{coin y z}} bα ) (f* {{coin x y}} bβ)
*f (compIsBiInv (suc zero) ((x , y , z) , g , g' , f , f') α β bα bβ) = compn ((suc zero)) ((((x , y , z) , g' , g , f' , f))) (*f ⦃ coin y z ⦄ bα) (*f ⦃ coin x y ⦄ bβ)
fR (compIsBiInv (suc zero) ((x , y , z) , g , g' , f , f') α β bα bβ) = {!!}
fL (compIsBiInv (suc zero) ((x , y , z) , g , g' , f , f') α β bα bβ) = {!!}
fRBiInv (compIsBiInv (suc zero) ((x , y , z) , g , g' , f , f') α β bα bβ) = {!!}
fLBiInv (compIsBiInv (suc zero) ((x , y , z) , g , g' , f , f') α β bα bβ) = {!!}
f* (compIsBiInv (suc (suc zero)) (a@((x , y , z) , g , g' , f , f') , α , α' , β , β') A B bA bB) = compn (suc (suc zero)) ((a , α' , α , β' , β)) (f* ⦃ Composable.coin (coin y z) g g' ⦄ bA) (f* ⦃ Composable.coin (coin x y) f f' ⦄ bB)
*f (compIsBiInv (suc (suc zero)) (((x , y , z) , g , g' , f , f') , α , α' , β , β') A B bA bB) = {!!}
fR (compIsBiInv (suc (suc zero)) (((x , y , z) , g , g' , f , f') , α , α' , β , β') A B bA bB) = {!!}
fL (compIsBiInv (suc (suc zero)) (((x , y , z) , g , g' , f , f') , α , α' , β , β') A B bA bB) = {!!}
fRBiInv (compIsBiInv (suc (suc zero)) (((x , y , z) , g , g' , f , f') , α , α' , β , β') A B bA bB) = {!!}
fLBiInv (compIsBiInv (suc (suc zero)) (((x , y , z) , g , g' , f , f') , α , α' , β , β') A B bA bB) = {!!}
compIsBiInv (suc (suc (suc n))) a A B bA bB = {!!}
