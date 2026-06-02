{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module LLPOAttemptLLMAided where
-- LLPO over ℕ∞, concluded from the finite/cofinite model.
--
-- Given the Stone-duality axiom `sd` and `fs` (an injective Boolean-algebra map
-- induces a surjection on spectra), LLPO follows from the model map
--   splitFC : ℕfinCofinBA → ℕfinCofinBA × ℕfinCofinBA,   I ↦ (evens of I, odds of I)
-- (EvenOddSplit): it has a trivial kernel, hence is injective, so its spectrum
-- action is surjective; transported across the Stone isos this is a surjection
-- ℕ∞ ⊎ ℕ∞ → ℕ∞ whose fibres yield the LLPO disjunction directly (SplitNaturality).

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

open import EvenOddSplit using (splitFC ; splitFC-kernel)
open import SplitNaturality using (evenNaturality ; oddNaturality)
open import SpNfcIso using (σ)

module LLPOProof (sd : StoneDualityAxiom) (fs : formalSurjectionsAreSurjectionsAxiom) where

  -- LLPO over ℕ∞ (sequences hitting 1 at most once).
  LLPOExplicitAt : ℕ∞ → Type
  LLPOExplicitAt (α , _) =
    (∀ (n : ℕ) → α (double n) ≡ false) ⊎ (∀ (n : ℕ) → α (suc $ double n) ≡ false)

  LLPO : Type
  LLPO = (x : ℕ∞) → ∥ LLPOExplicitAt x ∥₁

  private ℕfc = ℕfinCofinBA

  ℕfcω : Booleω
  ℕfcω = ℕfc , ℕfinCofinIsCountablyPresented

  -- `ℕfc ×BR ℕfc` is again countably presented, by the direct algebraic proof
  -- (orthogonal-idempotent decomposition) `ProductClosureLocal.Booleω-closed-×BR`.
  --
  -- Alternative idea (not used here): a Boolean algebra is countably presented
  -- iff it is overtly discrete, and overtly discrete spaces are closed under
  -- products; that route would instead supply
  --   odiscClosedUnderProducts : (A B : BooleanRing ℓ-zero)
  --     → is-countably-presented-alt A → is-countably-presented-alt B
  --     → is-countably-presented-alt (A ×BR B)
  ℕfcProdω : Booleω
  ℕfcProdω = (ℕfc ×BR ℕfc) , ProductClosureLocal.Booleω-closed-×BR ℕfcω ℕfcω

  -- splitFC has trivial kernel (EvenOddSplit.splitFC-kernel) ⇒ injective.
  splitInj : isInjectiveBoolHom ℕfcω ℕfcProdω splitFC
  splitInj x y = RingHomTheory.ker≡0→inj (CommRingHom→RingHom splitFC)
                   (λ {z} → splitFC-kernel z) {x} {y}

  -- ⇒ its spectrum action γ ↦ γ ∘cr splitFC is surjective (this is `fs`).
  SpSplit : SpGeneralBooleanRing (ℕfc ×BR ℕfc) → SpGeneralBooleanRing ℕfc
  SpSplit γ = γ ∘cr splitFC
  SpSplitSurj : isSurjection SpSplit
  SpSplitSurj = fs ℕfcω ℕfcProdω splitFC splitInj

  -- TEMPORARY HOTFIX: σ⊎ uses the local `StoneSums.SpProd≅SpSum`, which proves
  -- Sp(A ×BR B) ≅ Sp A ⊎ Sp B directly via idempotents in 2.  The intended,
  -- nicer statement is categorical (Sp an anti-equivalence Booleω ≃ Stone^op, so
  -- products in Booleω become sums in Stone); see CategoricalSumsProducts.
  σ⊎ : Iso (SpGeneralBooleanRing (ℕfc ×BR ℕfc)) (ℕ∞ ⊎ ℕ∞)
  σ⊎ = compIso (StoneSums.SpProd≅SpSum ℕfc ℕfc) (⊎Iso σ σ)

  e' : ℕ∞ ⊎ ℕ∞ → ℕ∞
  e' = Iso.fun σ ∘ SpSplit ∘ Iso.inv σ⊎

  e'Surj : isSurjection e'
  e'Surj = snd
    (compSurjection
      (Iso.inv σ⊎ , isEquiv→isSurjection (snd (isoToEquiv (invIso σ⊎))))
      (compSurjection
        (SpSplit , SpSplitSurj)
        (Iso.fun σ , isEquiv→isSurjection (snd (isoToEquiv σ)))))

  -- A fibre of e' over x yields the LLPO disjunct for x: e'(inl β) is the even
  -- split (0 on every odd index), e'(inr β) the odd split (0 on every even
  -- index), by SplitNaturality.  Only one coordinate of the fibre is inspected.
  e'-fibre→LLPO : (x : ℕ∞) → fiber e' x → LLPOExplicitAt x
  e'-fibre→LLPO x (inl β , p) = inr λ k →
    sym (cong (λ y → fst y (suc (double k))) p)
    ∙ funExt⁻ (evenNaturality (Iso.inv σ β)) (suc (double k))
    ∙ evenOddElim-odd k
  e'-fibre→LLPO x (inr β , p) = inl λ k →
    sym (cong (λ y → fst y (double k)) p)
    ∙ funExt⁻ (oddNaturality (Iso.inv σ β)) (double k)
    ∙ evenOddElim-even k

  llpo : LLPO
  llpo x = PT.map (e'-fibre→LLPO x) (e'Surj x)
