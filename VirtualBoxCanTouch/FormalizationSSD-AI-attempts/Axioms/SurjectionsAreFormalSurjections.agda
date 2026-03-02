{-# OPTIONS --cubical --guardedness #-}

module Axioms.SurjectionsAreFormalSurjections where

open import BasicDefinitions
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Functions.Surjection


open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Axioms.StoneDuality 

isInjectiveBoolHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isInjectiveBoolHom B C g = (x y : ⟨ fst B ⟩) → fst g x ≡ fst g y → x ≡ y
-- Fact : it's sufficient to show that f x = 0 → x = 0. 


isSurjectiveSpHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isSurjectiveSpHom B C g = isSurjection ((λ (γ : Sp C) → γ ∘cr g) :> (Sp C → Sp B) ) 
-- Note: this map can be phrased in a more categorical way, it's the action of Sp. 

formalSurjectionsAreSurjectionsAxiom : Type (ℓ-suc ℓ-zero)
formalSurjectionsAreSurjectionsAxiom = 
  (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isInjectiveBoolHom B C g → isSurjectiveSpHom B C g
--
--surjectionsAreFormallySurjecive : (B C : Booleω) (g : BoolHom (fst B) (fst C)) → isSurjectiveSpHom B C g → isInjectiveBoolHom B C g 
--surjectionsAreFormallySurjecive B C g ∘gSurj = {! !} 
---- This should be a standard categorical fact. 


