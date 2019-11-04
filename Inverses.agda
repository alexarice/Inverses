{-# OPTIONS --with-K --safe #-}

module Inverses where
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Axiom.UniquenessOfIdentityProofs.WithK

record GlobSet (_cells : ℕ → Set) : Set₁ where
  field
    source : {m mp : ℕ} → (suc mp ≡ m) → m cells → mp cells
    target : {m mp : ℕ} → (suc mp ≡ m) → m cells → mp cells
    sourceCompat : {m0 m2 : ℕ} → (pf : 2 + m0 ≡ m2) → {x : m2 cells} → source refl (source pf x) ≡ source refl (target pf x)
    targetCompat : {m0 m2 : ℕ} → (pf : 2 + m0 ≡ m2) → {x : m2 cells} → target refl (source pf x) ≡ target refl (source pf x)

open GlobSet {{...}}

compat : {_cells : ℕ → Set} {{_ : GlobSet _cells}} → (n : ℕ) → {m mp : ℕ} → (pf : 1 + n + mp ≡ m) → (f g : m cells) → Set
compat zero pf f g = source pf f ≡ target pf g
compat (suc n) {suc .(suc (n + mp))} {mp} refl f g = compat n {suc (n + mp)} {mp} refl (source refl f) (source refl g) × compat n {suc (n + mp)} {mp} refl (target refl f) (target refl g)

record GlobSet* (_cells : ℕ → Set): Set₂ where
  field
    {{gs}} : GlobSet _cells
    id : {n : ℕ} → (x : n cells) → (suc n) cells
    idsource : {n : ℕ} {x : n cells} → source refl (id x) ≡ x
    idtarget : {n : ℕ} {x : n cells} → target refl (id x) ≡ x
    comp : (n : ℕ) → {m mp : ℕ} → (pf : 1 + n + mp ≡ m) (f g : m cells) → compat n {m} {mp} pf f g → m cells

open GlobSet* {{...}}

record BiInvertible {_cells : ℕ → Set} {{_ : GlobSet* (_cells)}} {m mp : ℕ} (pf : suc mp ≡ m) (f : m cells) : Set₁ where
  coinductive
  field
    f* : m cells
    f*source : source pf f* ≡ target pf f
    f*target : target pf f* ≡ source pf f
    *f : m cells
    *fsource : source pf *f ≡ target pf f
    *ftarget : target pf *f ≡ source pf f
    fR : suc m cells
    fRsource : source refl fR ≡ comp zero {m} {mp} pf f f* (sym f*target)
    fRtarget : target (cong suc pf) fR ≡ id (target pf f)
    fL : suc m cells
    fLsource : source refl fR ≡ comp zero {m} {mp} pf *f f *fsource
    fLtarget : target (cong suc pf) fL ≡ id (target pf f)
    {{fRCoIn}} : BiInvertible (cong suc pf) fR
    {{fLCoIn}} : BiInvertible (cong suc pf) fL

open BiInvertible {{...}}

record HCat (_cells : ℕ → Set): Set₂ where
  field
    {{gs*}} : GlobSet* _cells
    ƛ : {m : ℕ} → (f : (suc m) cells) → ((suc(suc m)) cells)
    ƛsource : {m : ℕ} → (f : (suc m) cells) → source refl (ƛ f) ≡ comp zero refl (id (target refl f)) f idsource
    ƛtarget : {m : ℕ} → (f : (suc m) cells) → target refl (ƛ f) ≡ f
    ƛBiInv : {m : ℕ} → (f : (suc m) cells) → BiInvertible refl (ƛ f)

open HCat {{...}}

congcomp : { _cells : ℕ → Set } {{_ : GlobSet* _cells}} {m mp : ℕ} → (pf : suc mp ≡ m) → {f g h j : m cells} {x : compat zero pf f g} {y : compat zero pf h j} → f ≡ h → g ≡ j → comp zero pf f g x ≡ comp zero pf h j y
congcomp pf {f} {g} {_} {_} {x} {y} refl refl = cong (comp zero pf f g) (uip x y)

idBiInv : {_cells : ℕ → Set} {{_ : HCat (_cells)}} {m : ℕ} (x : m cells) → BiInvertible refl (id x)
BiInvertible.f* (idBiInv x) = id x
BiInvertible.f*source (idBiInv x) = trans idsource (sym idtarget)
BiInvertible.f*target (idBiInv x) = trans idtarget (sym idsource)
BiInvertible.*f (idBiInv x) = id x
BiInvertible.*fsource (idBiInv x) = trans idsource (sym idtarget)
BiInvertible.*ftarget (idBiInv x) = trans idtarget (sym idsource)
BiInvertible.fR (idBiInv x) = ƛ (id x)
BiInvertible.fRsource (idBiInv x) = trans (ƛsource (id x)) (congcomp refl (cong id idtarget) refl)
BiInvertible.fRtarget (idBiInv x) = trans (ƛtarget (id x)) (cong id (sym idtarget))
BiInvertible.fL (idBiInv x) = ƛ (id x)
BiInvertible.fLsource (idBiInv x) = trans (ƛsource (id x)) (congcomp refl (cong id idtarget) refl)
BiInvertible.fLtarget (idBiInv x) =  trans (ƛtarget (id x)) (cong id (sym idtarget))
BiInvertible.fRCoIn (idBiInv x) = ƛBiInv (id x)
BiInvertible.fLCoIn (idBiInv x) = ƛBiInv (id x)
