{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module BooleanRing.BooleanRingQuotients.CommRingReindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Univalence

import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Boole.EquivHelper

-- Reindexing: if σ : Iso X Y, then R /Im f ≅ R /Im (f ∘ Iso.inv σ)
module reindexCR {ℓ : Level} {R : CommRing ℓ} {X Y : Type ℓ} (σ : Iso X Y) (f : X → ⟨ R ⟩) where
  open CommRingStr ⦃...⦄
  instance
    _ = snd R
    _ = snd (R IQ./Im f)
    _ = snd (R IQ./Im (f ∘ Iso.inv σ))

  f' : Y → ⟨ R ⟩
  f' = f ∘ Iso.inv σ

  fwdKills : (x : X) → IQ.quotientImageHom R f' $cr f x ≡ 0r
  fwdKills x = subst (λ a → IQ.quotientImageHom R f' $cr a ≡ 0r)
    (cong f (Iso.ret σ x))
    (IQ.zeroOnImage R f' (Iso.fun σ x))

  fwd : CommRingHom (R IQ./Im f) (R IQ./Im f')
  fwd = IQ.inducedHom R f (IQ.quotientImageHom R f') fwdKills

  bwdKills : (y : Y) → IQ.quotientImageHom R f $cr f' y ≡ 0r
  bwdKills y = IQ.zeroOnImage R f (Iso.inv σ y)

  bwd : CommRingHom (R IQ./Im f') (R IQ./Im f)
  bwd = IQ.inducedHom R f' (IQ.quotientImageHom R f) bwdKills

  fwd∘π : fwd ∘cr IQ.quotientImageHom R f ≡ IQ.quotientImageHom R f'
  fwd∘π = IQ.evalInduce R

  bwd∘π : bwd ∘cr IQ.quotientImageHom R f' ≡ IQ.quotientImageHom R f
  bwd∘π = IQ.evalInduce R

  ret∘π : (bwd ∘cr fwd) ∘cr IQ.quotientImageHom R f ≡
          idCommRingHom (R IQ./Im f) ∘cr IQ.quotientImageHom R f
  ret∘π =
    (bwd ∘cr fwd) ∘cr IQ.quotientImageHom R f
      ≡⟨ CommRingHom≡ refl ⟩
    bwd ∘cr (fwd ∘cr IQ.quotientImageHom R f)
      ≡⟨ cong (bwd ∘cr_) fwd∘π ⟩
    bwd ∘cr IQ.quotientImageHom R f'
      ≡⟨ bwd∘π ⟩
    IQ.quotientImageHom R f
      ≡⟨ sym (idCompCommRingHom (IQ.quotientImageHom R f)) ⟩
    idCommRingHom _ ∘cr IQ.quotientImageHom R f ∎

  sec∘π : (fwd ∘cr bwd) ∘cr IQ.quotientImageHom R f' ≡
          idCommRingHom (R IQ./Im f') ∘cr IQ.quotientImageHom R f'
  sec∘π =
    (fwd ∘cr bwd) ∘cr IQ.quotientImageHom R f'
      ≡⟨ CommRingHom≡ refl ⟩
    fwd ∘cr (bwd ∘cr IQ.quotientImageHom R f')
      ≡⟨ cong (fwd ∘cr_) bwd∘π ⟩
    fwd ∘cr IQ.quotientImageHom R f
      ≡⟨ fwd∘π ⟩
    IQ.quotientImageHom R f'
      ≡⟨ sym (idCompCommRingHom (IQ.quotientImageHom R f')) ⟩
    idCommRingHom _ ∘cr IQ.quotientImageHom R f' ∎

  ret : bwd ∘cr fwd ≡ idCommRingHom (R IQ./Im f)
  ret = IQ.quotientImageHomEpi R ret∘π

  sec : fwd ∘cr bwd ≡ idCommRingHom (R IQ./Im f')
  sec = IQ.quotientImageHomEpi R sec∘π

  reindexEquivCR : CommRingEquiv (R IQ./Im f) (R IQ./Im f')
  reindexEquivCR = isoToCommRingEquiv fwd (fst bwd)
    (funExt⁻ (cong fst sec)) (funExt⁻ (cong fst ret))

-- Quotient compatible with equivalence: if R ≅ S then R /Im h ≅ S /Im (e ∘ h)
module equivQuotCR {ℓ : Level} {R S : CommRing ℓ} (e : CommRingEquiv R S)
  {X : Type ℓ} (h : X → ⟨ R ⟩) where
  open CommRingStr ⦃...⦄
  instance
    _ = snd R
    _ = snd S
    _ = snd (R IQ./Im h)
    _ = snd (S IQ./Im (fst (fst e) ∘ h))

  eFwd : ⟨ R ⟩ → ⟨ S ⟩
  eFwd = fst (fst e)

  eBwd : ⟨ S ⟩ → ⟨ R ⟩
  eBwd = fst (fst (invCommRingEquiv R S e))

  eFwdHom : CommRingHom R S
  eFwdHom = fst (fst e) , snd e

  eBwdHom : CommRingHom S R
  eBwdHom = let e⁻¹ = invCommRingEquiv R S e in fst (fst e⁻¹) , snd e⁻¹

  eBwd∘eFwd : eBwdHom ∘cr eFwdHom ≡ idCommRingHom R
  eBwd∘eFwd = CommRingHom≡ (funExt (equivToIso (fst e) .Iso.ret))

  eFwd∘eBwd : eFwdHom ∘cr eBwdHom ≡ idCommRingHom S
  eFwd∘eBwd = CommRingHom≡ (funExt (equivToIso (fst e) .Iso.sec))

  φ : CommRingHom R (S IQ./Im (eFwd ∘ h))
  φ = IQ.quotientImageHom S (eFwd ∘ h) ∘cr eFwdHom

  φKills : (x : X) → φ $cr h x ≡ 0r
  φKills x = IQ.zeroOnImage S (eFwd ∘ h) x

  fwdQ : CommRingHom (R IQ./Im h) (S IQ./Im (eFwd ∘ h))
  fwdQ = IQ.inducedHom R h φ φKills

  ψ : CommRingHom S (R IQ./Im h)
  ψ = IQ.quotientImageHom R h ∘cr eBwdHom

  ψKills : (x : X) → ψ $cr (eFwd (h x)) ≡ 0r
  ψKills x = cong (fst (IQ.quotientImageHom R h)) (funExt⁻ (cong fst eBwd∘eFwd) (h x))
    ∙ IQ.zeroOnImage R h x

  bwdQ : CommRingHom (S IQ./Im (eFwd ∘ h)) (R IQ./Im h)
  bwdQ = IQ.inducedHom S (eFwd ∘ h) ψ ψKills

  fwdQ∘π : fwdQ ∘cr IQ.quotientImageHom R h ≡ φ
  fwdQ∘π = IQ.evalInduce R

  bwdQ∘π : bwdQ ∘cr IQ.quotientImageHom S (eFwd ∘ h) ≡ ψ
  bwdQ∘π = IQ.evalInduce S

  ret∘π : (bwdQ ∘cr fwdQ) ∘cr IQ.quotientImageHom R h ≡
    idCommRingHom (R IQ./Im h) ∘cr IQ.quotientImageHom R h
  ret∘π =
    (bwdQ ∘cr fwdQ) ∘cr IQ.quotientImageHom R h
      ≡⟨ CommRingHom≡ refl ⟩
    bwdQ ∘cr (fwdQ ∘cr IQ.quotientImageHom R h)
      ≡⟨ cong (bwdQ ∘cr_) fwdQ∘π ⟩
    bwdQ ∘cr (IQ.quotientImageHom S (eFwd ∘ h) ∘cr eFwdHom)
      ≡⟨ CommRingHom≡ refl ⟩
    (bwdQ ∘cr IQ.quotientImageHom S (eFwd ∘ h)) ∘cr eFwdHom
      ≡⟨ cong (_∘cr eFwdHom) bwdQ∘π ⟩
    (IQ.quotientImageHom R h ∘cr eBwdHom) ∘cr eFwdHom
      ≡⟨ CommRingHom≡ refl ⟩
    IQ.quotientImageHom R h ∘cr (eBwdHom ∘cr eFwdHom)
      ≡⟨ cong (IQ.quotientImageHom R h ∘cr_) eBwd∘eFwd ⟩
    IQ.quotientImageHom R h ∘cr idCommRingHom R
      ≡⟨ CommRingHom≡ refl ⟩
    IQ.quotientImageHom R h
      ≡⟨ sym (idCompCommRingHom (IQ.quotientImageHom R h)) ⟩
    idCommRingHom _ ∘cr IQ.quotientImageHom R h ∎

  sec∘π : (fwdQ ∘cr bwdQ) ∘cr IQ.quotientImageHom S (eFwd ∘ h) ≡
    idCommRingHom (S IQ./Im (eFwd ∘ h)) ∘cr IQ.quotientImageHom S (eFwd ∘ h)
  sec∘π =
    (fwdQ ∘cr bwdQ) ∘cr IQ.quotientImageHom S (eFwd ∘ h)
      ≡⟨ CommRingHom≡ refl ⟩
    fwdQ ∘cr (bwdQ ∘cr IQ.quotientImageHom S (eFwd ∘ h))
      ≡⟨ cong (fwdQ ∘cr_) bwdQ∘π ⟩
    fwdQ ∘cr (IQ.quotientImageHom R h ∘cr eBwdHom)
      ≡⟨ CommRingHom≡ refl ⟩
    (fwdQ ∘cr IQ.quotientImageHom R h) ∘cr eBwdHom
      ≡⟨ cong (_∘cr eBwdHom) fwdQ∘π ⟩
    (IQ.quotientImageHom S (eFwd ∘ h) ∘cr eFwdHom) ∘cr eBwdHom
      ≡⟨ CommRingHom≡ refl ⟩
    IQ.quotientImageHom S (eFwd ∘ h) ∘cr (eFwdHom ∘cr eBwdHom)
      ≡⟨ cong (IQ.quotientImageHom S (eFwd ∘ h) ∘cr_) eFwd∘eBwd ⟩
    IQ.quotientImageHom S (eFwd ∘ h) ∘cr idCommRingHom S
      ≡⟨ CommRingHom≡ refl ⟩
    IQ.quotientImageHom S (eFwd ∘ h)
      ≡⟨ sym (idCompCommRingHom (IQ.quotientImageHom S (eFwd ∘ h))) ⟩
    idCommRingHom _ ∘cr IQ.quotientImageHom S (eFwd ∘ h) ∎

  retQ : bwdQ ∘cr fwdQ ≡ idCommRingHom (R IQ./Im h)
  retQ = IQ.quotientImageHomEpi R ret∘π

  secQ : fwdQ ∘cr bwdQ ≡ idCommRingHom (S IQ./Im (eFwd ∘ h))
  secQ = IQ.quotientImageHomEpi S sec∘π

  equivQuotientCR : CommRingEquiv (R IQ./Im h) (S IQ./Im (eFwd ∘ h))
  equivQuotientCR = isoToCommRingEquiv fwdQ (fst bwdQ)
    (funExt⁻ (cong fst secQ)) (funExt⁻ (cong fst retQ))
