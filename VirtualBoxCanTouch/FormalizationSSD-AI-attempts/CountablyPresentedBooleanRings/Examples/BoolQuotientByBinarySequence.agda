{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.Examples.BoolQuotientByBinarySequence where 

open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.Examples.Bool
open import Cubical.Data.Empty
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Algebra.BooleanRing

open import Cubical.Data.Nat
open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.QuotientConclusions
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.HITs.PropositionalTruncation
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import BasicDefinitions

module quotientByBinary (α : binarySequence) where
  quotientOf2ByBinary : BooleanRing ℓ-zero
  quotientOf2ByBinary = BoolBR QB./Im α

  presentation : has-countable-presentation quotientOf2ByBinary
  presentation = ⊥ , count⊥ , ℕ , countℕ , fst (fst 2≃free⊥) ∘ α , EquivQuotBR 2≃free⊥ α

  total : countablyPresentedBooleanRing 
  total = quotientOf2ByBinary , ∣ presentation ∣₁ 

2/α : binarySequence → countablyPresentedBooleanRing 
2/α = quotientByBinary.total

