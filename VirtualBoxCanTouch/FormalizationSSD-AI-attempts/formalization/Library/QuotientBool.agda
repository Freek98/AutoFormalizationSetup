{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module formalization.Library.QuotientBool where
{- This module re-exports from the canonical location for backwards compatibility -}

open import formalization.Library.BooleanRing.BooleanRingQuotients.QuotientBool public

-- Additional definitions not in the canonical module:
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Quotient.Base

module _ {ℓ : Level} {B : BooleanRing ℓ} {X : Type ℓ} {f : X → ⟨ B ⟩} where
  private
    R = BooleanRing→CommRing B

  opaque
    unfolding _/Im_ quotientImageHom
    fromKernel : {x : ⟨ B ⟩} → fst quotientImageHom x ≡ BooleanRingStr.𝟘 (snd (B /Im f))
      → IQ.generatedIdeal R f x
    fromKernel {x} p = subst (λ J → fst (fst J x)) (kernel≡I (IQ.genIdeal R f)) p

    toKernel : {x : ⟨ B ⟩} → IQ.generatedIdeal R f x
      → fst quotientImageHom x ≡ BooleanRingStr.𝟘 (snd (B /Im f))
    toKernel {x} p = zeroOnIdeal (IQ.genIdeal R f) x p
