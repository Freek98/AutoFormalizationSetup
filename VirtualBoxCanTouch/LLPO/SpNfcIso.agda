{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module SpNfcIso where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
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
open import BasicDefinitions using (binarySequence)

SpEq : Iso (SpGeneralBooleanRing ℕfinCofinBA) (SpGeneralBooleanRing presentation)
SpEq = invIso (CatIso→Iso (op-Iso⁻ {C = SET ℓ-zero}
              (preserveIsosF {F = SpGeneralFunctor} pres≅ℕfc)))
  where
    pres≅ℕfc : CatIso BACat presentation ℕfinCofinBA
    pres≅ℕfc = BAIso≅BAEquiv presentation ℕfinCofinBA .Iso.inv ℕFinCof=Presentation

σ : Iso (SpGeneralBooleanRing ℕfinCofinBA) ℕ∞
σ = compIso SpEq neededIso

toℕ∞seq : SpGeneralBooleanRing ℕfinCofinBA → binarySequence
toℕ∞seq γ n = γ $cr singleton n

σfun≡toℕ∞seq : (γ : SpGeneralBooleanRing ℕfinCofinBA) → fst (Iso.fun σ γ) ≡ toℕ∞seq γ
σfun≡toℕ∞seq γ = funExt λ n → cong (fst γ) $
   (fst (fst ℕFinCof=Presentation) (quotientImageHom $cr generator n)) 
     ≡⟨ funExt⁻ (cong fst (evalInduce ℕfinCofinBA)) (generator n) ⟩
   (freeℕ→ℕFinCof $cr generator n) 
     ≡⟨ eval-gen n ⟩
   singleton n ∎

