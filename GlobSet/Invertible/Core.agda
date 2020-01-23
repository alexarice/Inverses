{-# OPTIONS --without-K --safe --sized-types #-}

module GlobSet.Invertible.Core where

open import GlobSet
open import GlobSet.Composition

record Invertible {a : Level}
                  (i : Size)
                  {G : GlobSet a i}
                  (c : Composable i G)
                  (j : Size< i)
                  {x y : cells G}
                  (f : cells (morphisms G j x y)) : Set (suc a)

record InvertibleCell {a : Level}
                      (i : Size)
                      {G : GlobSet a i}
                      (c : Composable i G)
                      (j : Size< i)
                      (x y : cells G) : Set (suc a) where
  coinductive
  field
    cell : cells (morphisms G j x y)
    invert : Invertible i c j cell

record Invertible {a} i {G} c j {x} {y} f where
  coinductive
  field
    finv : cells (morphisms G j y x)
    fR : (k : Size< j) → InvertibleCell j (compHigher c j x x) k (comp1 c f finv) (id c j x)
    fL : (k : Size< j) → InvertibleCell j (compHigher c j y y) k (comp1 c finv f) (id c j y)

open InvertibleCell public
open Invertible public
