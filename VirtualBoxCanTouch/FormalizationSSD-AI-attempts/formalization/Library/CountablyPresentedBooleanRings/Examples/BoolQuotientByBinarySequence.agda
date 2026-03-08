{-# OPTIONS --cubical --guardedness #-}
module formalization.Library.CountablyPresentedBooleanRings.Examples.BoolQuotientByBinarySequence where 

open import formalization.Library.CountablyPresentedBooleanRings.Definitions
open import formalization.Library.CountablyPresentedBooleanRings.Examples.Bool
open import Cubical.Data.Empty
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Algebra.BooleanRing

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Algebra.CommRing
open import formalization.Library.BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import formalization.Library.BooleanRing.BooleanRingQuotients.QuotientConclusions
open import Cubical.Foundations.Structure
open import Cubical.Functions.Surjection
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation
import Cubical.HITs.PropositionalTruncation as PT
open import formalization.Library.CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import formalization.Library.BasicDefinitions

module quotientByBinary (α : binarySequence) where
  quotientOf2ByBinary : BooleanRing ℓ-zero
  quotientOf2ByBinary = BoolBR /Im α

  presentation : has-countable-presentation quotientOf2ByBinary
  presentation = ⊥ , count⊥ , ℕ , countℕ , fst (fst 2≃free⊥) ∘ α , EquivQuotBR 2≃free⊥ α

  total : countablyPresentedBooleanRing 
  total = quotientOf2ByBinary , ∣ (has-countable-presentation→has-freeℕ-presentation quotientOf2ByBinary presentation) ∣₁ 

  open BooleanRingStr (snd quotientOf2ByBinary)
  open IsCommRingHom  {S = snd (BooleanRing→CommRing quotientOf2ByBinary)} (snd quotientImageHom)

  max2inQuotient : ∀ (b : ⟨ quotientOf2ByBinary ⟩ ) → ∥ (b ≡ 𝟘) ⊎ (b ≡ 𝟙) ∥₁ 
  max2inQuotient b = PT.map fiberb→b=0∨1 (quotientImageHomSurjective b) where
    fiberb→b=0∨1 : fiber (fst quotientImageHom) b → (b ≡ 𝟘) ⊎ (b ≡ 𝟙)
    fiberb→b=0∨1 (false , fc=b) = inl (sym fc=b ∙ pres0)
    fiberb→b=0∨1 (true  , fc=b) = inr (sym fc=b ∙ pres1) 

2/α : binarySequence → countablyPresentedBooleanRing 
2/α = quotientByBinary.total



