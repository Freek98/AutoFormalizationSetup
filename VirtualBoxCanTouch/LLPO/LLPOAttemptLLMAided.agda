{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module LLPOAttemptLLMAided where
-- made in collaboration with LLM. 
open import CountablyPresentedBooleanRings.Examples.NFinCofin
open import BooleanRing.SubBooleanRing
open import Parity
open import CategoryTheory.StuffFromStoneAboutBAs
open import Cubical.Categories.Functor
open import Cubical.Data.Bool renaming (_≟_ to _=B_) hiding (_≤_ ; _≥_)
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import QuickFixes

open import BooleanRing.BooleanRingMaps
open import BooleanRing.FreeBooleanRing.FreeBool
import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.UniversalProperty
open import BooleanRing.BoolAlgMorphism

open import BasicDefinitions

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties using (module RingHomTheory)

open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import CountablyPresentedBooleanRings.Definitions
open import BooleanRing.ProductBA
open import Axioms.SurjectionsAreFormalSurjections
open import Axioms.StoneDuality
open import StoneSpaces.Spectrum

-- The following are LOCAL modules kept here (rather than in the FormalizationSSD
-- library) so that this folder is portable against a clean git checkout; each is
-- a temporary library workaround documented in LIBRARY_CHANGES.md.
open import NinftyExtras using (ℕ∞)          -- adds the Stone iso missing in Ninfty
import StoneSums                             -- Sp(A ×BR B) ≅ Sp A ⊎ Sp B  (see σ⊎)
import ProductClosureLocal                   -- algebraic product-closure (fixes ProductClosure)

open import EvenOddSplit using (splitHom ; splitHom-kernel)
open import SplitNaturality using (evenNaturality ; oddNaturality ; splitIntoEvens ; splitIntoOdds ; toℕ∞seq)
open import SpNfcIso using (σ)

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
    ≡⟨ funExt⁻ (evenNaturality (Iso.inv σ β)) (suc (double k)) ⟩
      splitIntoEvens (toℕ∞seq (Iso.inv σ β)) (suc (double k))
    ≡⟨ evenOddElim-odd k ⟩
      false ∎
  Spf-fibre→LLPO α (inr β , p) = inl λ k →
      fst α (double k)
    ≡⟨ sym (cong (λ y → fst y (double k)) p) ⟩
      fst (Spf (inr β)) (double k)
    ≡⟨ funExt⁻ (oddNaturality (Iso.inv σ β)) (double k) ⟩
      splitIntoOdds (toℕ∞seq (Iso.inv σ β)) (double k)
    ≡⟨ evenOddElim-even k ⟩
      false ∎

  llpo : LLPO
  llpo x = PT.map (Spf-fibre→LLPO x) (SpfSurj x)

llpoFromStoneDualityAndFormalSurjections : formalSurjectionsAreSurjectionsAxiom → LLPO
llpoFromStoneDualityAndFormalSurjections = LLPOProof.llpo
