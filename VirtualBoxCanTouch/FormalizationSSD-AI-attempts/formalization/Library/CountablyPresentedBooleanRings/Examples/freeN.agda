{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module formalization.Library.CountablyPresentedBooleanRings.Examples.freeN where
open import formalization.Library.CountablyPresentedBooleanRings.Definitions
open import formalization.Library.CountablyPresentedBooleanRings.Examples.Bool
open import formalization.Library.BooleanRing.FreeBooleanRing.FreeBool
open import formalization.Library.BooleanRing.AlgebraicFacts
open import formalization.Library.BooleanRing.BoolAlgMorphism
open import Cubical.Foundations.Equiv
open import Cubical.Tactics.NatSolver
open import Cubical.Tactics.CommRingSolver
open import formalization.Library.BooleanRing.BooleanRingMaps
open import formalization.Library.BooleanRing.SubBooleanRing
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_) 
open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Bool

open import Cubical.Data.Sum
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import formalization.Library.BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import formalization.Library.BooleanRing.BooleanRingQuotients.QuotientConclusions
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import formalization.Library.CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import formalization.Library.BasicDefinitions
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.Data.Bool renaming ( _≟_ to _=B_) hiding (_≤_ ; _≥_)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕ_)
open import Cubical.Algebra.CommRing.Instances.Unit
open import formalization.Library.QuickFixes

open BooleanAlgebraStr ⦃...⦄
open BooleanRingStr ⦃...⦄

freeℕ : BooleanRing ℓ-zero
ℙℕ = binarySequence , booleanStructureOnBinarySequences


