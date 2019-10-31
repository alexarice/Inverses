module Inverses where
open import Data.Nat
open import Relation.Binary.PropositionalEquality.Core


record GlobSet : Set₁ where
  field
    _cells : ℕ → Set
    source : {n : ℕ} → (suc n) cells → n cells
    target : {n : ℕ} → (suc n) cells → n cells
    sourceCompat : {n : ℕ} {x : (suc (suc n)) cells} → source (source x) ≡ source (target x)
    targetCompat : {n : ℕ} {x : (suc (suc n)) cells} → target (source x) ≡ target (source x)
