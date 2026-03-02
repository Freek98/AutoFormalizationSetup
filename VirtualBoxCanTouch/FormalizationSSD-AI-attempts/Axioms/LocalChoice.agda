{-# OPTIONS --cubical --guardedness #-}

module Axioms.LocalChoice where 

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
open import Axioms.SurjectionsAreFormalSurjections

isSurjectiveSpMap : {B C : Booleω} → (Sp C → Sp B) → Type ℓ-zero
isSurjectiveSpMap {B} {C} = isSurjection


LocalChoiceAxiom : Type (ℓ-suc ℓ-zero)
LocalChoiceAxiom = (B : Booleω) (P : Sp B → Type ℓ-zero)
  → ((s : Sp B) → ∥ P s ∥₁)
  → ∥ Σ[ C ∈ Booleω ] Σ[ q ∈ (Sp C → Sp B) ]
      (isSurjection q × ((t : Sp C) → P (q t))) ∥₁

