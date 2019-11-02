module Inverses where
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality.Core
open import Axiom.UniquenessOfIdentityProofs.WithK

record GlobSet (_cells : ℕ → Set) : Set₁ where
  field
    source : {n : ℕ} → (suc n) cells → n cells
    target : {n : ℕ} → (suc n) cells → n cells
    sourceCompat : {n : ℕ} {x : (suc (suc n)) cells} → source (source x) ≡ source (target x)
    targetCompat : {n : ℕ} {x : (suc (suc n)) cells} → target (source x) ≡ target (source x)

open GlobSet {{...}}

compat : {_cells : ℕ → Set} {{_ : GlobSet _cells}} → (n : ℕ) → {m : ℕ} → (f g : (n + (suc m)) cells) → Set
compat zero f g = source f ≡ target g
compat (suc n) f g = compat n (source f) (source g) × compat n (target f) (target g)

record GlobSet* (_cells : ℕ → Set): Set₂ where
  field
    {{gs}} : GlobSet _cells
    id : {n : ℕ} → (x : n cells) → (suc n) cells
    idsource : {n : ℕ} {x : n cells} → source (id x) ≡ x
    idtarget : {n : ℕ} {x : n cells} → target (id x) ≡ x
    comp : (n : ℕ) → {m : ℕ} → (f g : (n + suc m) cells) → compat n f g → (suc m) cells

open GlobSet* {{...}}

record BiInvertible {_cells : ℕ → Set} {{_ : GlobSet* (_cells)}} {m : ℕ} (f : (suc m) cells) : Set₁ where
  coinductive
  field
    f* : (suc m) cells
    f*source : source f* ≡ target f
    f*target : target f* ≡ source f
    *f : (suc m) cells
    *fsource : source *f ≡ target f
    *ftarget : target *f ≡ source f
    fR : (suc (suc m)) cells
    fRsource : source fR ≡ comp zero f f* (sym f*target)
    fRtarget : target fR ≡ id (target f)
    fL : (suc (suc m)) cells
    fLsource : source fR ≡ comp zero *f f *fsource
    {{fRCoIn}} : BiInvertible fR
    {{fLCoIn}} : BiInvertible fL

open BiInvertible {{...}}

record HCat (_cells : ℕ → Set): Set₂ where
  field
    {{gs*}} : GlobSet* _cells
    ƛ : {m : ℕ} → (f : (suc m) cells) → ((suc(suc m)) cells)
    ƛsource : {m : ℕ} → (f : (suc m) cells) → source (ƛ f) ≡ comp zero (id (target f)) f idsource
    ƛtarget : {m : ℕ} → (f : (suc m) cells) → target (ƛ f) ≡ f
    ƛBiInv : {m : ℕ} → (f : (suc m) cells) → BiInvertible (ƛ f)

open HCat {{...}}

congcomp : { _cells : ℕ → Set } {{_ : GlobSet* _cells}} {m : ℕ} {f g h j : (suc m) cells} {x : compat zero f g} {y : compat zero h j} → f ≡ h → g ≡ j → comp zero f g x ≡ comp zero h j y
congcomp {_} {_} {f} {g} {_} {_} {x} {y} refl refl = cong (comp zero f g) (uip x y)

idBiInv : {_cells : ℕ → Set} {{_ : HCat (_cells)}} {m : ℕ} (x : m cells) → BiInvertible (id x)
BiInvertible.f* (idBiInv x) = id x
BiInvertible.f*source (idBiInv x) = trans idsource (sym idtarget)
BiInvertible.f*target (idBiInv x) = trans idtarget (sym idsource)
BiInvertible.*f (idBiInv x) = id x
BiInvertible.*fsource (idBiInv x) = trans idsource (sym idtarget)
BiInvertible.*ftarget (idBiInv x) = trans idtarget (sym idsource)
BiInvertible.fR (idBiInv x) = ƛ (id x)
BiInvertible.fRsource (idBiInv x) = trans (ƛsource (id x)) (congcomp (cong id idtarget) refl)
BiInvertible.fRtarget (idBiInv x) = trans (ƛtarget (id x)) (cong id (sym idtarget))
BiInvertible.fL (idBiInv x) = ƛ (id x)
BiInvertible.fLsource (idBiInv x) = trans (ƛsource (id x)) (congcomp (cong id idtarget) refl)
BiInvertible.fRCoIn (idBiInv x) = ƛBiInv (id x)
BiInvertible.fLCoIn (idBiInv x) = ƛBiInv (id x)
