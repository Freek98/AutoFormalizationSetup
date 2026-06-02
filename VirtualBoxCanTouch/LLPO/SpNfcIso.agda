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

open import BooleanRing.BooleanRingMaps
  using (BooleanEquivToHom ; BooleanEquivToHomInv
        ; BooleanEquivLeftInv ; BooleanEquivRightInv)
open import BooleanRing.FreeBooleanRing.FreeBool using (generator)
open import BooleanRing.BooleanRingQuotients.QuotientBool using (quotientImageHom ; evalInduce)
open import StoneSpaces.Spectrum using (SpGeneralBooleanRing)
open import StoneSpaces.Examples.Ninfty using (ℕ∞ ; neededIso ; Sp→BinarySequence)
open import CountablyPresentedBooleanRings.Examples.NFinCofin
  using (ℕfinCofinBA ; presentation ; ℕFinCof=Presentation ; module NFinCofinPresentation)
open NFinCofinPresentation using (singleton ; eval-gen ; freeℕ→ℕFinCof)
open import SplitNaturality using (toℕ∞seq)

private
  -- the Boolean-algebra iso `presentation ≅ ℕfinCofinBA`, as two homs + roundtrips
  e₊ : BoolHom presentation ℕfinCofinBA
  e₊ = BooleanEquivToHom    presentation ℕfinCofinBA ℕFinCof=Presentation
  e₋ : BoolHom ℕfinCofinBA presentation
  e₋ = BooleanEquivToHomInv presentation ℕfinCofinBA ℕFinCof=Presentation

-- Sp applied to that BA-iso (contravariant ⇒ precomposition): Sp(ℕfinCofinBA) ≅ Sp(presentation)
SpEq : Iso (SpGeneralBooleanRing ℕfinCofinBA) (SpGeneralBooleanRing presentation)
SpEq .Iso.fun γ = γ ∘cr e₊
SpEq .Iso.inv δ = δ ∘cr e₋
SpEq .Iso.sec δ = CommRingHom≡ (cong (fst δ ∘_)
  (cong fst (BooleanEquivLeftInv  presentation ℕfinCofinBA ℕFinCof=Presentation)))
SpEq .Iso.ret γ = CommRingHom≡ (cong (fst γ ∘_)
  (cong fst (BooleanEquivRightInv presentation ℕfinCofinBA ℕFinCof=Presentation)))

-- the transported Stone iso
σ : Iso (SpGeneralBooleanRing ℕfinCofinBA) ℕ∞
σ = compIso SpEq neededIso

-- bridge: the transported read-off equals reading a point off on the singleton generators
σfun≡toℕ∞seq : (γ : SpGeneralBooleanRing ℕfinCofinBA) → fst (Iso.fun σ γ) ≡ toℕ∞seq γ
σfun≡toℕ∞seq γ = funExt λ n →
    γ $cr (e₊ $cr (quotientImageHom $cr generator n))
  ≡⟨ cong (λ b → γ $cr b) (funExt⁻ (cong fst e₊∘π≡φ) (generator n)) ⟩
    γ $cr (freeℕ→ℕFinCof $cr generator n)
  ≡⟨ cong (λ b → γ $cr b) (eval-gen n) ⟩
    γ $cr singleton n ∎
  where
    -- e₊ is (definitionally, by η) the induced map `inducedHom ℕfinCofinBA freeℕ→ℕFinCof _`,
    -- so its composite with the quotient map is the free extension `freeℕ→ℕFinCof`.
    e₊∘π≡φ : e₊ ∘cr quotientImageHom ≡ freeℕ→ℕFinCof
    e₊∘π≡φ = evalInduce ℕfinCofinBA
