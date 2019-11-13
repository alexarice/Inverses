{-# OPTIONS --with-K --safe #-}

module Inverses where
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Axiom.UniquenessOfIdentityProofs.WithK
open import Data.Product
open import Agda.Primitive

infixr 4 _·_

_·_ : {a : Level} {A : Set a} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_·_ = trans

transport : {a : Level} {A B : Set} → A ≡ B → A → B
transport refl x = x

record GlobSet (_cells : ℕ → Set) : Set₁ where
  field
    source : {m mp : ℕ} → (suc mp ≡ m) → m cells → mp cells
    target : {m mp : ℕ} → (suc mp ≡ m) → m cells → mp cells
    sourceCompat : {m0 m2 : ℕ} → (pf : 2 + m0 ≡ m2) → {x : m2 cells} → source refl (source pf x) ≡ source refl (target pf x)
    targetCompat : {m0 m2 : ℕ} → (pf : 2 + m0 ≡ m2) → {x : m2 cells} → target refl (source pf x) ≡ target refl (source pf x)

open GlobSet {{...}}

compat : {_cells : ℕ → Set} {{_ : GlobSet _cells}} → (n : ℕ) → {m mp : ℕ} → (1 + n + mp ≡ m) → (f g : m cells) → Set
compat zero pf f g = source pf f ≡ target pf g
compat (suc n) pf f g = compat n refl (source pf f) (source pf g) × compat n refl (target pf f) (target pf g)

compatUIP : {_cells : ℕ → Set} {{_ : GlobSet _cells}} {n : ℕ} {m mp : ℕ} {pf : 1 + n + mp ≡ m} {f g : m cells} (x y : compat n pf f g) → x ≡ y
compatUIP {_} {zero} x y = uip x y
compatUIP {n = suc n} (fst , snd) (fst₁ , snd₁) = cong₂ _,_ (compatUIP fst fst₁) (compatUIP snd snd₁)

record GlobSet* (_cells : ℕ → Set): Set₂ where
  field
    {{gs}} : GlobSet _cells
    id : {n : ℕ} → (x : n cells) → (suc n) cells
    idsource : {n : ℕ} {x : n cells} → source refl (id x) ≡ x
    idtarget : {n : ℕ} {x : n cells} → target refl (id x) ≡ x
    comp : (n : ℕ) → {m mp : ℕ} → (pf : 1 + n + mp ≡ m) (f g : m cells) → compat n pf f g → m cells
    comp0source : {m mp : ℕ} {pf : 1 + mp ≡ m} {f g : m cells} {com : compat zero pf f g} → source pf (comp zero pf f g com) ≡ source pf g
    comp0target : {m mp : ℕ} {pf : 1 + mp ≡ m} {f g : m cells} {com : compat zero pf f g} → target pf (comp zero pf f g com) ≡ target pf f
    compnsource : {n m mp : ℕ} {pf : 2 + n + mp ≡ m} {f g : m cells} {com : compat (suc n) pf f g} → source pf (comp (suc n) pf f g com) ≡ comp n refl (source pf f) (source pf g) (proj₁ com)
    compntarget : {n m mp : ℕ} {pf : 2 + n + mp ≡ m} {f g : m cells} {com : compat (suc n) pf f g} → target pf (comp (suc n) pf f g com) ≡ comp n refl (target pf f) (target pf g) (proj₂ com)

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
    fRCoIn : BiInvertible (cong suc pf) fR
    fLCoIn : BiInvertible (cong suc pf) fL

open BiInvertible

record HCat (_cells : ℕ → Set): Set₂ where
  field
    {{gs*}} : GlobSet* _cells
    ƛ : {m : ℕ} → (f : (suc m) cells) → ((suc(suc m)) cells)
    ƛsource : {m : ℕ} → (f : (suc m) cells) → source refl (ƛ f) ≡ comp zero refl (id (target refl f)) f idsource
    ƛtarget : {m : ℕ} → (f : (suc m) cells) → target refl (ƛ f) ≡ f
    ƛBiInv : {m : ℕ} → (f : (suc m) cells) → BiInvertible refl (ƛ f)
    i : {n : ℕ} {m mp : ℕ} (pf : 1 + (suc n) + mp ≡ m) → (f g h j : m cells) → (comfg : compat (suc n) pf f g) → (comhj : compat (suc n) pf h j) → (compat zero pf (comp (suc n) pf f g comfg) (comp (suc n) pf h j comhj)) → (comfh : compat zero pf f h) → (comgj : compat zero pf g j) → (compat (suc n) pf (comp zero pf f h comfh) (comp zero pf g j comgj)) → (suc m cells)
    isource : {n : ℕ} {m mp : ℕ} (pf : 1 + (suc n) + mp ≡ m) → (f g h j : m cells) → (comfg : compat (suc n) pf f g) → (comhj : compat (suc n) pf h j) → (com1 : compat zero pf (comp (suc n) pf f g comfg) (comp (suc n) pf h j comhj)) → (comfh : compat zero pf f h) → (comgj : compat zero pf g j) → (com2 : compat (suc n) pf (comp zero pf f h comfh) (comp zero pf g j comgj)) → source refl (i pf f g h j comfg comhj com1 comfh comgj com2) ≡ comp zero pf (comp (suc n) pf f g comfg) (comp (suc n) pf h j comhj) com1
    itarget : {n : ℕ} {m mp : ℕ} (pf : 1 + (suc n) + mp ≡ m) → (f g h j : m cells) → (comfg : compat (suc n) pf f g) → (comhj : compat (suc n) pf h j) → (com1 : compat zero pf (comp (suc n) pf f g comfg) (comp (suc n) pf h j comhj)) → (comfh : compat zero pf f h) → (comgj : compat zero pf g j) → (com2 : compat (suc n) pf (comp zero pf f h comfh) (comp zero pf g j comgj)) → target refl (i pf f g h j comfg comhj com1 comfh comgj com2) ≡ comp (suc n) pf (comp zero pf f h comfh) (comp zero pf g j comgj) com2
    iBiInv : {n : ℕ} {m mp : ℕ} (pf : 1 + (suc n) + mp ≡ m) → (f g h j : m cells) → (comfg : compat (suc n) pf f g) → (comhj : compat (suc n) pf h j) → (com1 : compat zero pf (comp (suc n) pf f g comfg) (comp (suc n) pf h j comhj)) → (comfh : compat zero pf f h) → (comgj : compat zero pf g j) → (com2 : compat (suc n) pf (comp zero pf f h comfh) (comp zero pf g j comgj)) → BiInvertible refl (i pf f g h j comfg comhj com1 comfh comgj com2)
    ex : {n : ℕ} {m mp : ℕ} (pf : 1 + (suc n) + mp ≡ m) → (f g : m cells) → (compat (suc n) pf f g) → (compat (suc (suc n)) (cong suc pf) (id f) (id g)) → suc (suc m) cells
    exsource : {n : ℕ} {m mp : ℕ} (pf : 1 + (suc n) + mp ≡ m) → (f g : m cells) → (com1 : compat (suc n) pf f g) → (com2 : compat (suc (suc n)) (cong suc pf) (id f) (id g)) → source refl (ex pf f g com1 com2) ≡ comp (suc (suc n)) (cong suc pf) (id f) (id g) com2
    extarget : {n : ℕ} {m mp : ℕ} (pf : 1 + (suc n) + mp ≡ m) → (f g : m cells) → (com1 : compat (suc n) pf f g) → (com2 : compat (suc (suc n)) (cong suc pf) (id f) (id g)) → target refl (ex pf f g com1 com2) ≡ id (comp (suc n) pf f g com1)

open HCat {{...}}

congcomp : (n : ℕ) { _cells : ℕ → Set } {{_ : GlobSet* _cells}} {m mp : ℕ} → (pf : 1 + n + mp ≡ m) → {f g h j : m cells} {x : compat n pf f g} {y : compat n pf h j} → f ≡ h → g ≡ j → comp n pf f g x ≡ comp n pf h j y
congcomp n refl {f} {g} {_} {_} {x} {y} refl refl = cong (comp n refl f g) (compatUIP x y)

idBiInv : {_cells : ℕ → Set} {{_ : HCat (_cells)}} {m : ℕ} (x : m cells) → BiInvertible refl (id x)
BiInvertible.f* (idBiInv x) = id x
BiInvertible.f*source (idBiInv x) = idsource · sym idtarget
BiInvertible.f*target (idBiInv x) = idtarget · sym idsource
BiInvertible.*f (idBiInv x) = id x
BiInvertible.*fsource (idBiInv x) = idsource · sym idtarget
BiInvertible.*ftarget (idBiInv x) = idtarget · sym idsource
BiInvertible.fR (idBiInv x) = ƛ (id x)
BiInvertible.fRsource (idBiInv x) = ƛsource (id x) · congcomp zero refl (cong id idtarget) refl
BiInvertible.fRtarget (idBiInv x) = ƛtarget (id x) · cong id (sym idtarget)
BiInvertible.fL (idBiInv x) = ƛ (id x)
BiInvertible.fLsource (idBiInv x) = ƛsource (id x) · congcomp zero refl (cong id idtarget) refl
BiInvertible.fLtarget (idBiInv x) = ƛtarget (id x) · cong id (sym idtarget)
BiInvertible.fRCoIn (idBiInv x) = ƛBiInv (id x)
BiInvertible.fLCoIn (idBiInv x) = ƛBiInv (id x)


compBiInv : {_cells : ℕ → Set} {{h : HCat (_cells)}} {m mp : ℕ} → (n : ℕ) → (pf : 1 + n + mp ≡ m) → (f g : m cells) → (BiInvertible pf f) → (BiInvertible pf g) → (com : compat n pf f g) → BiInvertible pf (comp n pf f g com)
compBiInv zero pf f g bf bg com = {!!}
f* (compBiInv (suc n) refl f g bf bg (fst , snd)) = comp (suc n) refl (f* bf) (f* bg) (transport (cong₂ (compat n refl) (sym (f*source bf)) (sym (f*source bg))) snd , transport (cong₂ (compat n refl) (sym (f*target bf)) (sym (f*target bg))) fst)
f*source (compBiInv (suc n) refl f g bf bg com) = compnsource · congcomp n refl (f*source bf) (f*source bg) · sym compntarget
f*target (compBiInv (suc n) refl f g bf bg com) = compntarget · congcomp n refl (f*target bf) (f*target bg) · sym compnsource
*f (compBiInv (suc n) refl f g bf bg (fst , snd)) = comp (suc n) refl (*f bf) (*f bg) ((transport (cong₂ (compat n refl) (sym (*fsource bf)) (sym (*fsource bg))) snd) , (transport (cong₂ (compat n refl) (sym (*ftarget bf)) (sym (*ftarget bg))) fst))
*fsource (compBiInv (suc n) refl f g bf bg com) = compnsource · congcomp n refl (*fsource bf) (*fsource bg) · sym compntarget
*ftarget (compBiInv (suc n) refl f g bf bg com) = compntarget · congcomp n refl (*ftarget bf) (*ftarget bg) · sym compnsource
fR (compBiInv (suc n) pf f g bf bg com) = comp zero refl (i pf f g (f* bf) (f* bg) com {!!} {!!} {!!} {!!} {!!}) (comp zero refl (comp (suc (suc n)) (cong suc pf) (fR bf) (fR bg) {!!}) (ex ? ? ? ? ?) {!!}) {!!}
fRsource (compBiInv (suc n) pf f g bf bg com) = {!!}
fRtarget (compBiInv (suc n) pf f g bf bg com) = {!!}
fL (compBiInv (suc n) pf f g bf bg com) = {!!}
fLsource (compBiInv (suc n) pf f g bf bg com) = {!!}
fLtarget (compBiInv (suc n) pf f g bf bg com) = {!!}
fRCoIn (compBiInv (suc n) pf f g bf bg com) = {!!}
fLCoIn (compBiInv (suc n) pf f g bf bg com) = {!!}
