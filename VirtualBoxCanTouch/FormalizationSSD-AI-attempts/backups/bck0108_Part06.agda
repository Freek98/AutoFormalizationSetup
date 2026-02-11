{-# OPTIONS --cubical --guardedness #-}

module work.Part06 where

open import work.Part05 public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma
import QuotientBool as QB
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA)
open import Axioms.StoneDuality using (Booleω; Sp; hasStoneStr)
open import Cubical.Data.Bool using (Bool)

open import BooleanRing.FreeBooleanRing.freeBATerms using (equalityFromEqualityOnGenerators)

SpB∞-to-ℕ∞-injective : (h₁ h₂ : Sp B∞-Booleω) →
  SpB∞-to-ℕ∞ h₁ ≡ SpB∞-to-ℕ∞ h₂ → h₁ ≡ h₂
SpB∞-to-ℕ∞-injective h₁ h₂ seq-eq = B∞-hom-eq
  where
  seq-eq-pointwise : (n : ℕ) → h₁ $cr (g∞ n) ≡ h₂ $cr (g∞ n)
  seq-eq-pointwise n = funExt⁻ (cong fst seq-eq) n

  h₁-free h₂-free : BoolHom (freeBA ℕ) BoolBR
  h₁-free = h₁ ∘cr π∞
  h₂-free = h₂ ∘cr π∞

  free-hom-eq : h₁-free ≡ h₂-free
  free-hom-eq = equalityFromEqualityOnGenerators BoolBR h₁-free h₂-free seq-eq-pointwise

  B∞-hom-eq : h₁ ≡ h₂
  B∞-hom-eq = CommRingHom≡ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = relB∞}
    (⟨ BoolBR ⟩ , BooleanRingStr.is-set (snd BoolBR))
    (cong fst free-hom-eq))

SpB∞-retraction : (h : Sp B∞-Booleω) → ℕ∞-to-SpB∞ (SpB∞-to-ℕ∞ h) ≡ h
SpB∞-retraction h = SpB∞-to-ℕ∞-injective (ℕ∞-to-SpB∞ (SpB∞-to-ℕ∞ h)) h
  (SpB∞-roundtrip (SpB∞-to-ℕ∞ h))

SpB∞≅ℕ∞ : Iso (Sp B∞-Booleω) ℕ∞
SpB∞≅ℕ∞ = iso SpB∞-to-ℕ∞ ℕ∞-to-SpB∞ SpB∞-roundtrip SpB∞-retraction

SpB∞≃ℕ∞ : Sp B∞-Booleω ≃ ℕ∞
SpB∞≃ℕ∞ = isoToEquiv SpB∞≅ℕ∞

ℕ∞-has-StoneStr : hasStoneStr ℕ∞
ℕ∞-has-StoneStr = B∞-Booleω , ua SpB∞≃ℕ∞

-- Bool is Stone (tex line 1527)
Bool-has-StoneStr : hasStoneStr Bool
Bool-has-StoneStr = Bool²-Booleω , ua Sp-Bool²≃Bool
