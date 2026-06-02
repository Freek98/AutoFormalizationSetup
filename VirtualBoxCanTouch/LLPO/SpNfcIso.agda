{-# OPTIONS --cubical --guardedness --lossy-unification #-}
-- The Stone iso for the finite/cofinite model: Sp(ℕfinCofinBA) ≅ ℕ∞.
--
-- Obtained by TRANSPORT from the upstream
--   neededIso : Iso (Sp presentation) ℕ∞                              (StoneSpaces.Examples.Ninfty)
-- across the Boolean-algebra iso
--   ℕFinCof=Presentation : BooleanRingEquiv presentation ℕfinCofinBA  (…Examples.NFinCofin)
-- pushed through the contravariant spectrum action (precomposition):
--   σ = Sp(ℕfinCofinBA) ──Sp e₊──▶ Sp(presentation) ──neededIso──▶ ℕ∞.
--
-- `σfun≡toℕ∞seq` records that the transported `Iso.fun σ` still reads a point off on the
-- singleton generators (= `toℕ∞seq`).  The main file's fibre proof needs this, because the
-- upstream read-off `Sp→BinarySequence` (via `generator`/`quotientImageHom`) agrees with the
-- local `toℕ∞seq` (via `singleton`) only propositionally — exactly `eval-gen`.
module SpNfcIso where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing using (CommRingHom≡ ; _∘cr_ ; _$cr_)
open import Cubical.Algebra.BooleanRing using (BoolHom)

-- `Sp` as a functor: the general "functors preserve isos" machinery
open import Cubical.Categories.Category.Base using (CatIso)
open import Cubical.Categories.Functor.Properties using (preserveIsosF)
open import Cubical.Categories.Isomorphism using (op-Iso⁻)
open import Cubical.Categories.Instances.Sets using (SET ; CatIso→Iso)

open import BooleanRing.BooleanRingMaps using (BooleanEquivToHom)
open import BooleanRing.FreeBooleanRing.FreeBool using (generator)
open import BooleanRing.BooleanRingQuotients.QuotientBool using (quotientImageHom ; evalInduce)
open import StoneSpaces.Spectrum using (SpGeneralBooleanRing)
open import CategoryTheory.StuffFromStoneAboutBAs using (BACat ; SpGeneralFunctor ; BAIso≅BAEquiv)
open import StoneSpaces.Examples.Ninfty using (ℕ∞ ; neededIso ; Sp→BinarySequence)
open import CountablyPresentedBooleanRings.Examples.NFinCofin
  using (ℕfinCofinBA ; presentation ; ℕFinCof=Presentation ; module NFinCofinPresentation)
open NFinCofinPresentation using (singleton ; eval-gen ; freeℕ→ℕFinCof)
open import SplitNaturality using (toℕ∞seq)

SpEq : Iso (SpGeneralBooleanRing ℕfinCofinBA) (SpGeneralBooleanRing presentation)
SpEq = invIso (CatIso→Iso (op-Iso⁻ {C = SET ℓ-zero}
              (preserveIsosF {F = SpGeneralFunctor} pres≅ℕfc)))
  where
    pres≅ℕfc : CatIso BACat presentation ℕfinCofinBA
    pres≅ℕfc = BAIso≅BAEquiv presentation ℕfinCofinBA .Iso.inv ℕFinCof=Presentation

σ : Iso (SpGeneralBooleanRing ℕfinCofinBA) ℕ∞
σ = compIso SpEq neededIso

-- bridge: the transported read-off equals reading a point off on the singleton generators
σfun≡toℕ∞seq : (γ : SpGeneralBooleanRing ℕfinCofinBA) → fst (Iso.fun σ γ) ≡ toℕ∞seq γ
σfun≡toℕ∞seq γ = funExt λ n →
    γ $cr (fst (fst ℕFinCof=Presentation) (quotientImageHom $cr generator n))
  ≡⟨ cong (λ b → γ $cr b) (funExt⁻ (cong fst e∘π≡φ) (generator n)) ⟩
    γ $cr (freeℕ→ℕFinCof $cr generator n)
  ≡⟨ cong (λ b → γ $cr b) (eval-gen n) ⟩
    γ $cr singleton n ∎
  where
    e∘π≡φ : (BooleanEquivToHom presentation ℕfinCofinBA ℕFinCof=Presentation) ∘cr quotientImageHom ≡ freeℕ→ℕFinCof
    e∘π≡φ = evalInduce ℕfinCofinBA
