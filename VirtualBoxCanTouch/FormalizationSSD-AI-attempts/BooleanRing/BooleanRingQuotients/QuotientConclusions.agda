{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module BooleanRing.BooleanRingQuotients.QuotientConclusions  where
{- We show that the quotient of a Boolean Ring agrees with that of the underlying commutative Ring -}

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing.Univalence
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ

import Cubical.Data.Sum as ⊎

open import QuotientBool as QB
open import BooleanRing.BoolRingUnivalence
open import BooleanRing.BooleanRingMaps
open import CommRingQuotients.RepeatedQuotient
open import CommRingQuotients.ReindexingQuotients
open import BasicDefinitions

private opaque
  unfolding QB._/Im_ QB.quotientImageHom
  QBAgreesWithCR : {ℓ : Level} {A : BooleanRing ℓ} → {X : Type ℓ} → {f : X → ⟨ A ⟩} →
    BooleanRing→CommRing (A QB./Im f) ≡ (BooleanRing→CommRing A) IQ./Im f
  QBAgreesWithCR = refl

private opaque
  unfolding QB.quotientImageHom QBAgreesWithCR
  sumWhenRestricted : {ℓ : Level} (A : BooleanRing ℓ) {X : Type ℓ} (f g : X → ⟨ A ⟩) →
    BooleanRing→CommRing (A QB./Im (⊎.rec f g)) ≡
    BooleanRing→CommRing ((A QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
  sumWhenRestricted A f g =
    BooleanRing→CommRing (A QB./Im (⊎.rec f g))
      ≡⟨ QBAgreesWithCR ⟩
    (BooleanRing→CommRing A) IQ./Im (⊎.rec f g)
      ≡⟨ (uaCommRing $ quotientConclusion (BooleanRing→CommRing A) f g) ⟩
      ((BooleanRing→CommRing A) IQ./Im f) IQ./Im
      ((fst $ IQ.quotientImageHom (BooleanRing→CommRing A) f)∘ g)
      ≡⟨ sym QBAgreesWithCR ⟩
    BooleanRing→CommRing ((A QB./Im f) QB./Im ( (fst $ QB.quotientImageHom {B = A} {f = f}) ∘ g)) ∎

quotientEquivBool : {ℓ : Level} {X : Type ℓ} (A : BooleanRing ℓ) (f g : X → ⟨ A ⟩ ) →
  A QB./Im (⊎.rec f g) ≡
  (A QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g)
quotientEquivBool A f g = uaBoolRing
  (invEq (CommRingPath _ _) (sumWhenRestricted A f g))

opaque
  unfolding QB._/Im_
  reindexwithEquiv : {ℓ : Level} {A : BooleanRing ℓ} {X Y : Type ℓ} (σ : Iso X Y) (f : X → ⟨ A ⟩) → BooleanRingEquiv (A QB./Im f) (A QB./Im (f ∘ Iso.inv σ))
  reindexwithEquiv σ f = reindexCR.reindexEquivCR σ f

opaque
  unfolding QB._/Im_
  EquivQuotBR : {ℓ : Level} {A B : BooleanRing ℓ} (e : BooleanRingEquiv A B)
    {X : Type ℓ} (h : X → ⟨ A ⟩) →
    BooleanRingEquiv (A QB./Im h) (B QB./Im ((fst (fst e))∘ h))
  EquivQuotBR = equivQuotCR.equivQuotientCR
