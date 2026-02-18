{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module BooleanRing.BooleanRingQuotients.QuotientConclusions  where
{- We show that the quotient of a Boolean Ring agrees with that of the underlying commutative Ring -}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing.Univalence

open import QuotientBool as QB
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ

open import BooleanRing.BooleanRingQuotients.QuotientCase

opaque
  unfolding QB._/Im_
  quotientCheck : (A : BooleanRing ℓ-zero) → {X : Type} → (f : X → ⟨ A ⟩ ) →
    (BooleanRing→CommRing A) IQ./Im f ≡ BooleanRing→CommRing (A QB./Im f)
  quotientCheck A f = refl

opaque
  unfolding QB._/Im_
  unfolding QB.quotientImageHom
  BoolQuotientEquiv : (A : BooleanRing ℓ-zero) (f g : ℕ → ⟨ A ⟩) →
    BooleanRing→CommRing (A QB./Im (⊎.rec f g)) ≡
    BooleanRing→CommRing ((A QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
  BoolQuotientEquiv A f g =
    sym (quotientCheck A (⊎.rec f g))
    ∙ uaCommRing (quotientConclusion (BooleanRing→CommRing A) f g)
    ∙ quotientCheck (A QB./Im f) ((fst (IQ.quotientImageHom (BooleanRing→CommRing A) f)) ∘ g)
