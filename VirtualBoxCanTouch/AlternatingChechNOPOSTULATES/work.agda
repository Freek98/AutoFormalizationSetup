{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module work where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.AbGroup
open import Cubical.Functions.Surjection

open import Trichotomy public

module CechComplex
  {ℓ : Level}
  {S : Type ℓ}
  {X : Type ℓ}
  (_<S_ : S → S → Type ℓ)
  (isSTO : IsStrictTotalOrder _<S_)
  (isSetX : isSet X)
  (q : S → X)
  (isSurjQ : isSurjection q)
  (A : X → AbGroup ℓ)
  where

  open import CechBase _<S_ isSTO isSetX q isSurjQ A public
  open import CechPermutations _<S_ isSTO isSetX q isSurjQ A public
  open import CechFaceMaps _<S_ isSTO isSetX q isSurjQ A public
  open import CechSorting _<S_ isSTO isSetX q isSurjQ A public
  open import CechProperties _<S_ isSTO isSetX q isSurjQ A public
  open import CechDSquared _<S_ isSTO isSetX q isSurjQ A public
