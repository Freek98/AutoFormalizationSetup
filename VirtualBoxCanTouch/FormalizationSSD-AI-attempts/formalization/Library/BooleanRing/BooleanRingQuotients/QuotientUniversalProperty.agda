{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module formalization.Library.BooleanRing.BooleanRingQuotients.QuotientUniversalProperty where

{- This module proves that any Boolean ring C with the universal property
   of B /Im f is equivalent to B /Im f. Concretely:

   Given:
     B : BooleanRing, f : X → ⟨ B ⟩  (quotient data)
     C : BooleanRing
     φ : BoolHom B C  (a map from B to C)
     φ-zero : φ kills Im(f)
     C-induce : for any S and g : BoolHom B S killing Im(f), a map C → S
     C-eval   : C-induce S g ∘cr φ ≡ g  (computation)
     C-unique : uniqueness of the induced map

   Conclude: BooleanRingEquiv (B /Im f) C
-}

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

module QuotientCharacterization
  (B : BooleanRing ℓ) {X : Type ℓ} (f : X → ⟨ B ⟩)
  (C : BooleanRing ℓ)
  (φ : BoolHom B C)
  (φ-zero : ∀ (x : X) → φ $cr (f x) ≡ BooleanRingStr.𝟘 (snd C))
  (C-induce : (S : BooleanRing ℓ) (g : BoolHom B S)
              (g-zero : ∀ (x : X) → g $cr (f x) ≡ BooleanRingStr.𝟘 (snd S))
              → BoolHom C S)
  (C-eval : (S : BooleanRing ℓ) (g : BoolHom B S)
            (g-zero : ∀ (x : X) → g $cr (f x) ≡ BooleanRingStr.𝟘 (snd S))
            → C-induce S g g-zero ∘cr φ ≡ g)
  (C-unique : (S : BooleanRing ℓ) (g : BoolHom B S)
              (g-zero : ∀ (x : X) → g $cr (f x) ≡ BooleanRingStr.𝟘 (snd S))
              (h : BoolHom C S) → g ≡ h ∘cr φ → C-induce S g g-zero ≡ h)
  where

  private
    Q = B /Im f
    π = quotientImageHom {f = f}
    π-zero = zeroOnImage {f = f}

  -- Q → C: Use Q's universal property, since φ : B → C kills Im(f)
  Q→C : BoolHom Q C
  Q→C = inducedHom C φ φ-zero

  -- C → Q: Use C's universal property, since π : B → Q kills Im(f)
  C→Q : BoolHom C Q
  C→Q = C-induce Q π π-zero

  -- Q→C ∘cr π ≡ φ (from Q's universal property)
  Q→C-comp : Q→C ∘cr π ≡ φ
  Q→C-comp = evalInduce {f = f} C

  -- C→Q ∘cr φ ≡ π (from C's universal property)
  C→Q-comp : C→Q ∘cr φ ≡ π
  C→Q-comp = C-eval Q π π-zero

  -- Roundtrip Q: C→Q ∘cr Q→C ≡ idBoolHom Q
  -- Strategy: use quotientImageHomEpi — show they agree when precomposed with π
  roundtripQ : C→Q ∘cr Q→C ≡ idBoolHom Q
  roundtripQ = CommRingHom≡ (quotientImageHomEpi {f = f} (⟨ Q ⟩ , BooleanRingStr.is-set (snd Q)) path)
    where
    -- fst (C→Q ∘cr Q→C) ∘ fst π
    -- = fst C→Q ∘ fst Q→C ∘ fst π
    -- = fst C→Q ∘ fst φ          (by Q→C-comp)
    -- = fst π                     (by C→Q-comp)
    path : fst (C→Q ∘cr Q→C) ∘ fst π ≡ fst (idBoolHom Q) ∘ fst π
    path =
      fst (C→Q ∘cr Q→C) ∘ fst π
        ≡⟨ cong (fst C→Q ∘_) (cong fst Q→C-comp) ⟩
      fst C→Q ∘ fst φ
        ≡⟨ cong fst C→Q-comp ⟩
      fst π ∎

  -- Roundtrip C: Q→C ∘cr C→Q ≡ idBoolHom C
  -- Strategy: both Q→C ∘cr C→Q and idC satisfy C's UP for (S=C, g=φ),
  -- so they are equal by C-unique
  roundtripC : Q→C ∘cr C→Q ≡ idBoolHom C
  roundtripC = sym (C-unique C φ φ-zero (Q→C ∘cr C→Q) compPath)
             ∙ C-unique C φ φ-zero (idBoolHom C) idPath
    where
    -- (Q→C ∘cr C→Q) ∘cr φ = Q→C ∘cr (C→Q ∘cr φ) = Q→C ∘cr π = φ
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

  -- Build the equivalence
  Q≃C-Iso : Iso ⟨ Q ⟩ ⟨ C ⟩
  Q≃C-Iso .Iso.fun = fst Q→C
  Q≃C-Iso .Iso.inv = fst C→Q
  Q≃C-Iso .Iso.sec c = funExt⁻ (cong fst roundtripC) c
  Q≃C-Iso .Iso.ret q = funExt⁻ (cong fst roundtripQ) q

  quotientUniversalPropertyEquiv : BooleanRingEquiv Q C
  quotientUniversalPropertyEquiv = (fst Q→C , isoToIsEquiv Q≃C-Iso) , snd Q→C
