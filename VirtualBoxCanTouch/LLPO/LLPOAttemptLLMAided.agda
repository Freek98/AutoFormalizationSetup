{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module LLPOAttemptLLMAided where
-- made in collaboration with LLM. 
open import CountablyPresentedBooleanRings.Examples.NFinCofin
open import StoneSpaces.Examples.Ninfty
open import Parity
open import Cubical.Data.Bool renaming (_≟_ to _=B_) hiding (_≤_ ; _≥_)

open import BooleanRing.BoolAlgMorphism

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (fiber)

open import Cubical.Algebra.CommRing

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import CountablyPresentedBooleanRings.Definitions
open import BooleanRing.ProductBA
open import Axioms.SurjectionsAreFormalSurjections
open import StoneSpaces.Spectrum

-- The following are LOCAL modules kept here (rather than in the FormalizationSSD
-- library) so that this folder is portable against a clean git checkout; each is
-- a temporary library workaround documented in LIBRARY_CHANGES.md.
import StoneSums            -- Sp(A ×BR B) ≅ Sp A ⊎ Sp B  (see σ⊎)
import ProductClosureLocal  -- algebraic product-closure (fixes ProductClosure)

open import EvenOddSplit using (splitHom ; splitHom-kernel)
open import SplitNaturality using (evenNaturality ; oddNaturality ; splitIntoEvens ; splitIntoOdds ; toℕ∞seq)
open import SpNfcIso using (σ ; σfun≡toℕ∞seq)

LLPOExplicitAt : ℕ∞ → Type
LLPOExplicitAt (α , _) =
  (∀ (n : ℕ) → α (double n) ≡ false) ⊎ (∀ (n : ℕ) → α (suc $ double n) ≡ false)

LLPO : Type
LLPO = (x : ℕ∞) → ∥ LLPOExplicitAt x ∥₁

B∞ : Booleω
B∞ = ℕfinCofinBA , ℕfinCofinIsCountablyPresented

module LLPOProof (formalSurjections : formalSurjectionsAreSurjectionsAxiom) where
  
  -- We make use of the product of B∞ with itself, and we need that countably presented boolean algebras are closed under products. Right now, we use an algebraic proof for this. 
  -- Another proof that we don't use is to show that a boolean algebra is countably presented iff it is overtly discrete and show that overtly discrete is closed under products. 
  B∞xB∞ : Booleω
  B∞xB∞ = B∞ ×Booleω B∞ where 
    open ProductClosureLocal

  -- We also use that Sp is an antiequivalence and thus 
  -- Sp(A ×BR B) ≅ Sp A ⊎ Sp B 
  -- Right now, we also use an algebraic proof for this. 
  -- It should be proven using categorical facts. 
  σ⊎ : Iso (SpGeneralBooleanRing (ℕfinCofinBA ×BR ℕfinCofinBA)) (ℕ∞ ⊎ ℕ∞)
  σ⊎ = compIso (StoneSums.SpProd≅SpSum ℕfinCofinBA ℕfinCofinBA) (⊎Iso σ σ)
 
  splitInj : isInjectiveBoolHom B∞ B∞xB∞ splitHom
  splitInj = ker≡0→injBoolHom B∞ B∞xB∞ splitHom splitHom-kernel 
  
  -- this is the action of Sp on morphisms
  SpSplit : SpGeneralBooleanRing (ℕfinCofinBA ×BR ℕfinCofinBA) → SpGeneralBooleanRing ℕfinCofinBA
  SpSplit γ = γ ∘cr splitHom

  SpSplitSurj : isSurjection SpSplit
  SpSplitSurj = formalSurjections B∞ B∞xB∞ splitHom splitInj

  Spf : ℕ∞ ⊎ ℕ∞ → ℕ∞
  Spf = Iso.fun σ ∘ SpSplit ∘ Iso.inv σ⊎

  SpfSurj : isSurjection Spf
  SpfSurj = snd
    (compSurjection
      (Iso→↠ (invIso σ⊎))
      (compSurjection
        (SpSplit , SpSplitSurj)
        (Iso→↠ σ)))
    where
    Iso→↠ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} → Iso X Y → X ↠ Y
    Iso→↠ i = Iso.fun i , isEquiv→isSurjection (snd (isoToEquiv i))

  Spf-fibre→LLPO : (α : ℕ∞) → fiber Spf α → LLPOExplicitAt α
  Spf-fibre→LLPO α (inl β , p) = inr λ k →
      fst α (suc (double k))
    ≡⟨ sym (cong (λ y → fst y (suc (double k))) p) ⟩
      fst (Spf (inl β)) (suc (double k))
    ≡⟨ funExt⁻ (σfun≡toℕ∞seq (SpSplit (Iso.inv σ⊎ (inl β)))) (suc (double k)) ⟩
      toℕ∞seq (SpSplit (Iso.inv σ⊎ (inl β))) (suc (double k))
    ≡⟨ funExt⁻ (evenNaturality (Iso.inv σ β)) (suc (double k)) ⟩
      splitIntoEvens (toℕ∞seq (Iso.inv σ β)) (suc (double k))
    ≡⟨ evenOddElim-odd k ⟩
      false ∎
  Spf-fibre→LLPO α (inr β , p) = inl λ k →
      fst α (double k)
    ≡⟨ sym (cong (λ y → fst y (double k)) p) ⟩
      fst (Spf (inr β)) (double k)
    ≡⟨ funExt⁻ (σfun≡toℕ∞seq (SpSplit (Iso.inv σ⊎ (inr β)))) (double k) ⟩
      toℕ∞seq (SpSplit (Iso.inv σ⊎ (inr β))) (double k)
    ≡⟨ funExt⁻ (oddNaturality (Iso.inv σ β)) (double k) ⟩
      splitIntoOdds (toℕ∞seq (Iso.inv σ β)) (double k)
    ≡⟨ evenOddElim-even k ⟩
      false ∎

  llpo : LLPO
  llpo x = PT.map (Spf-fibre→LLPO x) (SpfSurj x)

llpoFromStoneDualityAndFormalSurjections : formalSurjectionsAreSurjectionsAxiom → LLPO
llpoFromStoneDualityAndFormalSurjections = LLPOProof.llpo
