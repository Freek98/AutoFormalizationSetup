{-# OPTIONS --cubical --guardedness #-}

module PropositionalTopology.OpenClosedProps where
open import QuickFixes
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Logic
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary hiding (¬_)
open import QuickFixes
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import BasicDefinitions

import QuotientBool as QB
import Cubical.Data.Sum as ⊎

isOpenWitness : hProp ℓ-zero → Type₀
isOpenWitness P = Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ (Σ[ n ∈ ℕ ] α n ≡ true)

isOpenProp : hProp ℓ-zero → Type₀
isOpenProp P = ∥ isOpenWitness P ∥₁

isPropIsOpenProp : {P : hProp ℓ-zero} → isProp (isOpenProp P)
isPropIsOpenProp = squash₁

isClosedWitness : hProp ℓ-zero → Type₀
isClosedWitness P = Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) →  α n ≡ false)

isClosedProp : hProp ℓ-zero → Type₀
isClosedProp P = ∥ isClosedWitness P ∥₁ 

isPropIsClosedProp : {P : hProp ℓ-zero} → isProp (isClosedProp P)
isPropIsClosedProp = squash₁

Open : Type₁
Open = Σ[ P ∈ hProp ℓ-zero ] isOpenProp P

Closed : Type₁
Closed = Σ[ P ∈ hProp ℓ-zero ] isClosedProp P

negOpenWitnessIsClosedWitness : (P : hProp ℓ-zero) → isOpenWitness P → isClosedWitness (¬ P) 
negOpenWitnessIsClosedWitness P (α , P→Σα , Σα→P) = 
  α , ¬P→∀α , ∀α→¬P where
  ¬P→∀α : ⟨ ¬ P ⟩ → (n : ℕ) → α n ≡ false 
  ¬P→∀α ¬p n = ¬true→false (α n) λ αn=t → 
    ¬p (Σα→P (n , αn=t))
  ∀α→¬P : ((n : ℕ) → α n ≡ false) → ⟨ ¬ P ⟩ 
  ∀α→¬P ∀n¬αn p = case (P→Σα p) of 
    λ ((n , αn=t)) → true≢false $ 
    true ≡⟨ sym αn=t ⟩ α n ≡⟨ ∀n¬αn n ⟩ false ∎

negOpenIsClosed : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp (¬ P)
negOpenIsClosed P = PT.map (negOpenWitnessIsClosedWitness P)

decIsOpen : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isOpenProp P
decIsOpen P (yes p) = ∣ (λ _ → true) , (λ _ → 0 , refl) , (λ _ → p) ∣₁
decIsOpen P (no ¬p) = ∣ (λ _ → false) , (λ p₁ → ex-falso (¬p p₁)) , (λ x → ex-falso (false≢true (snd x))) ∣₁

decIsClosed : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isClosedProp P
decIsClosed P (yes p) = ∣ (λ _ → false) , (λ _ _ → refl) , (λ _ → p) ∣₁
decIsClosed P (no ¬p) = ∣ (λ _ → true) , (λ p₁ → ex-falso (¬p p₁)) , (λ f → ex-falso (true≢false (f 0))) ∣₁

