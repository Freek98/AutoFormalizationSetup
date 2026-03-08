{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module formalization.Library.BooleanRing.BooleanRingQuotients.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing

open import formalization.Library.BooleanRing.BooleanRingQuotients.QuotientBool
open import formalization.Library.BooleanRing.BooleanRingMaps
open import formalization.Library.BooleanRing.BoolRingUnivalence

private variable ℓ : Level

open BooleanRingStr

module UniversalProperty
  (B : BooleanRing ℓ) {X : Type ℓ} (f : X → ⟨ B ⟩)
  (C : BooleanRing ℓ)
  (φ : BoolHom B C)
  (φ-zero : ∀ (x : X) → φ $cr (f x) ≡ 𝟘 (snd C))
  (extension : (S : BooleanRing ℓ) (g : BoolHom B S)
               (g-zero : ∀ (x : X) → g $cr (f x) ≡ 𝟘 (snd S)) → 
               BoolHom C S)
  (commutes : (S : BooleanRing ℓ) (g : BoolHom B S)
              (g-zero : ∀ (x : X) → g $cr (f x) ≡ 𝟘 (snd S)) → 
              extension S g g-zero ∘cr φ ≡ g)
  (unique : (S : BooleanRing ℓ) (g : BoolHom B S)
            (g-zero : ∀ (x : X) → g $cr (f x) ≡ 𝟘 (snd S))
            (h : BoolHom C S) → g ≡ h ∘cr φ → extension S g g-zero ≡ h)
  where

  private
    Q = B /Im f
    π = quotientImageHom {f = f}
    π-zero = zeroOnImage {f = f}

  Q→C : BoolHom Q C
  Q→C = inducedHom C φ φ-zero

  C→Q : BoolHom C Q
  C→Q = extension Q π π-zero

  Q→C-comp : Q→C ∘cr π ≡ φ
  Q→C-comp = evalInduce {f = f} C

  C→Q-comp : C→Q ∘cr φ ≡ π
  C→Q-comp = commutes Q π π-zero

  roundtripQ : C→Q ∘cr Q→C ≡ idBoolHom Q
  roundtripQ = CommRingHom≡ (quotientImageHomEpi {f = f} (⟨ Q ⟩ , BooleanRingStr.is-set (snd Q)) path)
    where
    path : fst (C→Q ∘cr Q→C) ∘ fst π ≡ fst (idBoolHom Q) ∘ fst π
    path =
      fst (C→Q ∘cr Q→C) ∘ fst π
        ≡⟨ cong (fst C→Q ∘_) (cong fst Q→C-comp) ⟩
      fst C→Q ∘ fst φ
        ≡⟨ cong fst C→Q-comp ⟩
      fst π ∎

  roundtripC : Q→C ∘cr C→Q ≡ idBoolHom C
  roundtripC = sym (unique C φ φ-zero (Q→C ∘cr C→Q) compPath)
             ∙ unique C φ φ-zero (idBoolHom C) idPath
    where
    compPath : φ ≡ (Q→C ∘cr C→Q) ∘cr φ
    compPath =
      φ
        ≡⟨ sym Q→C-comp ⟩
      Q→C ∘cr π
        ≡⟨ cong (Q→C ∘cr_) (sym C→Q-comp) ⟩
      Q→C ∘cr (C→Q ∘cr φ)
        ≡⟨ compAssocCommRingHom φ C→Q Q→C ⟩
      (Q→C ∘cr C→Q) ∘cr φ ∎

    idPath : φ ≡ idBoolHom C ∘cr φ
    idPath = sym (CommRingHom≡ refl)

  Q≃C-Iso : Iso ⟨ Q ⟩ ⟨ C ⟩
  Q≃C-Iso .Iso.fun = fst Q→C
  Q≃C-Iso .Iso.inv = fst C→Q
  Q≃C-Iso .Iso.sec c = funExt⁻ (cong fst roundtripC) c
  Q≃C-Iso .Iso.ret q = funExt⁻ (cong fst roundtripQ) q

  quotientUniversalPropertyEquiv : BooleanRingEquiv Q C
  quotientUniversalPropertyEquiv = (fst Q→C , isoToIsEquiv Q≃C-Iso) , snd Q→C
