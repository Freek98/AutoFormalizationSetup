{-# OPTIONS --cubical --guardedness #-}

module work.Part02 where

open import work.Part01 public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Powerset using (_∈_)

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (discreteℕ; +∸)
import Cubical.Induction.WellFounded as WF
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Axioms.StoneDuality using (StoneDualityAxiom; Sp; Booleω)

import OmnisciencePrinciples.Markov as MarkovLib

open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; invBooleanRingEquiv)
open import CountablyPresentedBooleanRings.Examples.Bool using (is-cp-2)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA)
import QuotientBool as QB
open import BooleanRing.BoolRingUnivalence using (BoolRingPath)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
import Cubical.Data.Sum as ⊎

module SpectrumEmptyImpliesTrivial (SD : StoneDualityAxiom) (B : Booleω) (spEmpty : Sp B → ⊥) where
  open import Cubical.Foundations.Equiv
  open import Axioms.StoneDuality using (evaluationMap)

  emptyFunContr : isContr (Sp B → Bool)
  emptyFunContr = (λ sp → ex-falso (spEmpty sp)) , λ f → funExt (λ sp → ex-falso (spEmpty sp))

  B-contr : isContr ⟨ fst B ⟩
  B-contr = isOfHLevelRespectEquiv 0 (invEquiv (evaluationMap B , SD B)) emptyFunContr

  0≡1-in-B : BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B))
  0≡1-in-B = isContr→isProp B-contr _ _

open import Cubical.Algebra.CommRing.Properties using (compCommRingEquiv)

compBoolRingEquiv : (A B C : BooleanRing ℓ-zero)
                  → BooleanRingEquiv A B → BooleanRingEquiv B C → BooleanRingEquiv A C
compBoolRingEquiv A B C f g = compCommRingEquiv {A = BooleanRing→CommRing A} {B = BooleanRing→CommRing B} {C = BooleanRing→CommRing C} f g

open import Cubical.Algebra.CommRing.Univalence using (CommRingPath)

commRingPath→boolRingEquiv : (A B : BooleanRing ℓ-zero)
  → BooleanRing→CommRing A ≡ BooleanRing→CommRing B
  → BooleanRingEquiv A B
commRingPath→boolRingEquiv A B p = commRingEquivToEquiv , snd commRingEquivToEquiv'
  where
  commRingEquivToEquiv' : CommRingEquiv (BooleanRing→CommRing A) (BooleanRing→CommRing B)
  commRingEquivToEquiv' = invEq (CommRingPath _ _) p

  commRingEquivToEquiv : ⟨ A ⟩ ≃ ⟨ B ⟩
  commRingEquivToEquiv = fst commRingEquivToEquiv'

Bool-Booleω : Booleω
Bool-Booleω = BoolBR , ∣ is-cp-2 ∣₁

private
  idBoolHom-local : BoolHom BoolBR BoolBR
  fst idBoolHom-local = idfun Bool
  snd idBoolHom-local .IsCommRingHom.pres0 = refl
  snd idBoolHom-local .IsCommRingHom.pres1 = refl
  snd idBoolHom-local .IsCommRingHom.pres+ _ _ = refl
  snd idBoolHom-local .IsCommRingHom.pres· _ _ = refl
  snd idBoolHom-local .IsCommRingHom.pres- _ = refl

Sp-Bool-inhabited : ∥ Sp Bool-Booleω ∥₁
Sp-Bool-inhabited = ∣ idBoolHom-local ∣₁

quotientPreservesBooleω : (α : binarySequence) → ∥ has-Boole-ω' (BoolBR QB./Im α) ∥₁
quotientPreservesBooleω α = ∣ presentationWitness ∣₁
  where
  f₀ : ℕ → ⟨ freeBA ℕ ⟩
  f₀ = fst is-cp-2

  equiv : BooleanRingEquiv BoolBR (freeBA ℕ QB./Im f₀)
  equiv = snd is-cp-2

  π₀ : ⟨ freeBA ℕ ⟩ → ⟨ freeBA ℕ QB./Im f₀ ⟩
  π₀ = fst QB.quotientImageHom

  equiv⁻¹ : ⟨ freeBA ℕ QB./Im f₀ ⟩ → ⟨ BoolBR ⟩
  equiv⁻¹ = fst (invEquiv (fst equiv))

  embBR : ⟨ BoolBR ⟩ → ⟨ freeBA ℕ QB./Im f₀ ⟩
  embBR = fst (fst equiv)

  α' : ℕ → ⟨ freeBA ℕ QB./Im f₀ ⟩
  α' n = embBR (α n)

  open import BooleanRing.FreeBooleanRing.FreeBool using (generator)

  gen : ℕ → ⟨ freeBA ℕ ⟩
  gen = generator

  encode : ℕ ⊎ ℕ → ℕ
  encode = Iso.fun ℕ⊎ℕ≅ℕ

  decode : ℕ → ℕ ⊎ ℕ
  decode = Iso.inv ℕ⊎ℕ≅ℕ

  open BooleanRingStr (snd (freeBA ℕ))

  g : ℕ → ⟨ freeBA ℕ ⟩
  g n = if (α n) then 𝟙 else 𝟘

  h : ℕ → ⟨ freeBA ℕ ⟩
  h n with decode n
  ... | inl m = f₀ m   -- relations from the original presentation
  ... | inr m = g m    -- relations from α

  presentationWitness : has-Boole-ω' (BoolBR QB./Im α)
  presentationWitness = h , equivToPresentation
    where

    step2-path : BooleanRing→CommRing (freeBA ℕ QB./Im (⊎.rec f₀ g)) ≡
                 BooleanRing→CommRing ((freeBA ℕ QB./Im f₀) QB./Im (π₀ ∘ g))
    step2-path = BoolQuotientEquiv (freeBA ℕ) f₀ g

    step2-equiv : BooleanRingEquiv (freeBA ℕ QB./Im (⊎.rec f₀ g)) ((freeBA ℕ QB./Im f₀) QB./Im (π₀ ∘ g))
    step2-equiv = commRingPath→boolRingEquiv (freeBA ℕ QB./Im (⊎.rec f₀ g)) ((freeBA ℕ QB./Im f₀) QB./Im (π₀ ∘ g)) step2-path

    h≡rec∘decode-pointwise : (n : ℕ) → h n ≡ ⊎.rec f₀ g (decode n)
    h≡rec∘decode-pointwise n with decode n
    ... | inl m = refl
    ... | inr m = refl

    h≡rec∘decode : h ≡ (⊎.rec f₀ g) ∘ decode
    h≡rec∘decode = funExt h≡rec∘decode-pointwise

    import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
    R = BooleanRing→CommRing (freeBA ℕ)

    rec-of-decode : (n : ℕ) → ⊎.rec f₀ g (decode n) ≡ h n
    rec-of-decode n = sym (h≡rec∘decode-pointwise n)

    encode∘decode : (n : ℕ) → encode (decode n) ≡ n
    encode∘decode = Iso.sec ℕ⊎ℕ≅ℕ

    decode∘encode : (x : ℕ ⊎ ℕ) → decode (encode x) ≡ x
    decode∘encode = Iso.ret ℕ⊎ℕ≅ℕ

    rec-quotient : BooleanRing ℓ-zero
    rec-quotient = freeBA ℕ QB./Im (⊎.rec f₀ g)

    h-quotient : BooleanRing ℓ-zero
    h-quotient = freeBA ℕ QB./Im h

    π-rec : BoolHom (freeBA ℕ) rec-quotient
    π-rec = QB.quotientImageHom

    π-h : BoolHom (freeBA ℕ) h-quotient
    π-h = QB.quotientImageHom

    π-rec-sends-h-to-0 : (n : ℕ) → π-rec $cr (h n) ≡ BooleanRingStr.𝟘 (snd rec-quotient)
    π-rec-sends-h-to-0 n =
      π-rec $cr (h n)
        ≡⟨ cong (π-rec $cr_) (sym (rec-of-decode n)) ⟩
      π-rec $cr ((⊎.rec f₀ g) (decode n))
        ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = ⊎.rec f₀ g} (decode n) ⟩
      BooleanRingStr.𝟘 (snd rec-quotient) ∎

    step3-forward-hom : BoolHom h-quotient rec-quotient
    step3-forward-hom = QB.inducedHom {B = freeBA ℕ} {f = h} rec-quotient π-rec π-rec-sends-h-to-0

    rec-eq-h-encode : (x : ℕ ⊎ ℕ) → (⊎.rec f₀ g) x ≡ h (encode x)
    rec-eq-h-encode x =
      (⊎.rec f₀ g) x
        ≡⟨ cong (⊎.rec f₀ g) (sym (decode∘encode x)) ⟩
      (⊎.rec f₀ g) (decode (encode x))
        ≡⟨ rec-of-decode (encode x) ⟩
      h (encode x) ∎

    π-h-sends-rec-to-0 : (x : ℕ ⊎ ℕ) → π-h $cr ((⊎.rec f₀ g) x) ≡ BooleanRingStr.𝟘 (snd h-quotient)
    π-h-sends-rec-to-0 x =
      π-h $cr ((⊎.rec f₀ g) x)
        ≡⟨ cong (π-h $cr_) (rec-eq-h-encode x) ⟩
      π-h $cr (h (encode x))
        ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = h} (encode x) ⟩
      BooleanRingStr.𝟘 (snd h-quotient) ∎

    step3-backward-hom : BoolHom rec-quotient h-quotient
    step3-backward-hom = QB.inducedHom {B = freeBA ℕ} {f = ⊎.rec f₀ g} h-quotient π-h π-h-sends-rec-to-0

    step3-forward : ⟨ h-quotient ⟩ → ⟨ rec-quotient ⟩
    step3-forward = fst step3-forward-hom

    step3-backward : ⟨ rec-quotient ⟩ → ⟨ h-quotient ⟩
    step3-backward = fst step3-backward-hom

    step3-forward-eval : step3-forward-hom ∘cr π-h ≡ π-rec
    step3-forward-eval = QB.evalInduce {B = freeBA ℕ} {f = h} rec-quotient π-rec π-rec-sends-h-to-0

    step3-backward-eval : step3-backward-hom ∘cr π-rec ≡ π-h
    step3-backward-eval = QB.evalInduce {B = freeBA ℕ} {f = ⊎.rec f₀ g} h-quotient π-h π-h-sends-rec-to-0

    h-quotient-isSet : isSet ⟨ h-quotient ⟩
    h-quotient-isSet = BooleanRingStr.is-set (snd h-quotient)

    rec-quotient-isSet : isSet ⟨ rec-quotient ⟩
    rec-quotient-isSet = BooleanRingStr.is-set (snd rec-quotient)

    step3-backward∘forward-on-π : (x : ⟨ freeBA ℕ ⟩) → step3-backward (step3-forward (fst π-h x)) ≡ fst π-h x
    step3-backward∘forward-on-π x =
      step3-backward (step3-forward (fst π-h x))
        ≡⟨ cong step3-backward (cong (λ f → fst f x) step3-forward-eval) ⟩
      step3-backward (fst π-rec x)
        ≡⟨ cong (λ f → fst f x) step3-backward-eval ⟩
      fst π-h x ∎

    step3-backward∘forward-ext : (step3-backward ∘ step3-forward) ∘ fst π-h ≡ (λ x → x) ∘ fst π-h
    step3-backward∘forward-ext = funExt step3-backward∘forward-on-π

    step3-backward∘forward : (x : ⟨ h-quotient ⟩) → step3-backward (step3-forward x) ≡ x
    step3-backward∘forward = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = h} (⟨ h-quotient ⟩ , h-quotient-isSet) step3-backward∘forward-ext)

    step3-forward∘backward-on-π : (y : ⟨ freeBA ℕ ⟩) → step3-forward (step3-backward (fst π-rec y)) ≡ fst π-rec y
    step3-forward∘backward-on-π y =
      step3-forward (step3-backward (fst π-rec y))
        ≡⟨ cong step3-forward (cong (λ f → fst f y) step3-backward-eval) ⟩
      step3-forward (fst π-h y)
        ≡⟨ cong (λ f → fst f y) step3-forward-eval ⟩
      fst π-rec y ∎

    step3-forward∘backward-ext : (step3-forward ∘ step3-backward) ∘ fst π-rec ≡ (λ y → y) ∘ fst π-rec
    step3-forward∘backward-ext = funExt step3-forward∘backward-on-π

    step3-forward∘backward : (y : ⟨ rec-quotient ⟩) → step3-forward (step3-backward y) ≡ y
    step3-forward∘backward = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = ⊎.rec f₀ g} (⟨ rec-quotient ⟩ , rec-quotient-isSet) step3-forward∘backward-ext)

    step3-iso : Iso ⟨ h-quotient ⟩ ⟨ rec-quotient ⟩
    Iso.fun step3-iso = step3-forward
    Iso.inv step3-iso = step3-backward
    Iso.sec step3-iso = step3-forward∘backward
    Iso.ret step3-iso = step3-backward∘forward

    step3-equiv-fun : ⟨ h-quotient ⟩ ≃ ⟨ rec-quotient ⟩
    step3-equiv-fun = isoToEquiv step3-iso

    step3-equiv' : BooleanRingEquiv h-quotient rec-quotient
    step3-equiv' = step3-equiv-fun , snd step3-forward-hom

    step3-h-eq : freeBA ℕ QB./Im h ≡ freeBA ℕ QB./Im (⊎.rec f₀ g)
    step3-h-eq = equivFun (BoolRingPath h-quotient rec-quotient) step3-equiv'

    step3-equiv : BooleanRingEquiv (freeBA ℕ QB./Im h) (freeBA ℕ QB./Im (⊎.rec f₀ g))
    step3-equiv = invEq (BoolRingPath _ _) step3-h-eq

    target : BooleanRing ℓ-zero
    target = (freeBA ℕ QB./Im f₀) QB./Im α'

    embBR-hom : BoolHom BoolBR (freeBA ℕ QB./Im f₀)
    embBR-hom = fst (fst equiv) , snd equiv

    π-α' : BoolHom (freeBA ℕ QB./Im f₀) target
    π-α' = QB.quotientImageHom

    composite-hom : BoolHom BoolBR target
    composite-hom = π-α' ∘cr embBR-hom

    composite-sends-α-to-0 : (n : ℕ) → composite-hom $cr (α n) ≡ BooleanRingStr.𝟘 (snd target)
    composite-sends-α-to-0 n = QB.zeroOnImage {f = α'} n

    forward-hom : BoolHom (BoolBR QB./Im α) target
    forward-hom = QB.inducedHom target composite-hom composite-sends-α-to-0

    source : BooleanRing ℓ-zero
    source = BoolBR QB./Im α

    equiv⁻¹-hom : BoolHom (freeBA ℕ QB./Im f₀) BoolBR
    equiv⁻¹-hom = fst (fst (invBooleanRingEquiv BoolBR (freeBA ℕ QB./Im f₀) equiv)) ,
                  snd (invBooleanRingEquiv BoolBR (freeBA ℕ QB./Im f₀) equiv)

    π-α : BoolHom BoolBR source
    π-α = QB.quotientImageHom

    backward-composite : BoolHom (freeBA ℕ QB./Im f₀) source
    backward-composite = π-α ∘cr equiv⁻¹-hom

    backward-composite-sends-α'-to-0 : (n : ℕ) → backward-composite $cr (α' n) ≡ BooleanRingStr.𝟘 (snd source)
    backward-composite-sends-α'-to-0 n =
      backward-composite $cr (α' n)
        ≡⟨ refl ⟩
      π-α $cr (equiv⁻¹-hom $cr (embBR (α n)))
        ≡⟨ cong (π-α $cr_) (Iso.ret (equivToIso (fst equiv)) (α n)) ⟩
      π-α $cr (α n)
        ≡⟨ QB.zeroOnImage {f = α} n ⟩
      BooleanRingStr.𝟘 (snd source) ∎

    backward-hom : BoolHom target source
    backward-hom = QB.inducedHom source backward-composite backward-composite-sends-α'-to-0

    forward-fun : ⟨ source ⟩ → ⟨ target ⟩
    forward-fun = fst forward-hom

    backward-fun : ⟨ target ⟩ → ⟨ source ⟩
    backward-fun = fst backward-hom

    forward-eval : forward-hom ∘cr π-α ≡ composite-hom
    forward-eval = QB.evalInduce {B = BoolBR} {f = α} target composite-hom composite-sends-α-to-0

    backward-eval : backward-hom ∘cr π-α' ≡ backward-composite
    backward-eval = QB.evalInduce {B = freeBA ℕ QB./Im f₀} {f = α'} source backward-composite backward-composite-sends-α'-to-0

    equiv⁻¹∘embBR≡id : (x : Bool) → fst equiv⁻¹-hom (embBR x) ≡ x
    equiv⁻¹∘embBR≡id = Iso.ret (equivToIso (fst equiv))

    source-isSet : isSet ⟨ source ⟩
    source-isSet = is-set (snd source)
      where open BooleanRingStr

    target-isSet : isSet ⟨ target ⟩
    target-isSet = is-set (snd target)
      where open BooleanRingStr

    backward∘forward-on-π : (x : Bool) → backward-fun (forward-fun (fst π-α x)) ≡ fst π-α x
    backward∘forward-on-π x =
      backward-fun (forward-fun (fst π-α x))
        ≡⟨ cong backward-fun (cong (λ h → fst h x) forward-eval) ⟩
      backward-fun (fst composite-hom x)
        ≡⟨ refl ⟩  -- composite-hom = π-α' ∘ embBR-hom
      backward-fun (fst π-α' (embBR x))
        ≡⟨ cong (λ h → fst h (embBR x)) backward-eval ⟩
      fst backward-composite (embBR x)
        ≡⟨ refl ⟩  -- backward-composite = π-α ∘ equiv⁻¹-hom
      fst π-α (fst equiv⁻¹-hom (embBR x))
        ≡⟨ cong (fst π-α) (equiv⁻¹∘embBR≡id x) ⟩
      fst π-α x ∎

    backward∘forward-ext : (backward-fun ∘ forward-fun) ∘ fst π-α ≡ (λ x → x) ∘ fst π-α
    backward∘forward-ext = funExt backward∘forward-on-π

    backward∘forward : (x : ⟨ source ⟩) → backward-fun (forward-fun x) ≡ x
    backward∘forward = funExt⁻ (QB.quotientImageHomEpi {B = BoolBR} {f = α} (⟨ source ⟩ , source-isSet) backward∘forward-ext)

    embBR∘equiv⁻¹≡id : (y : ⟨ freeBA ℕ QB./Im f₀ ⟩) → embBR (fst equiv⁻¹-hom y) ≡ y
    embBR∘equiv⁻¹≡id = Iso.sec (equivToIso (fst equiv))

    forward∘backward-on-π : (y : ⟨ freeBA ℕ QB./Im f₀ ⟩) → forward-fun (backward-fun (fst π-α' y)) ≡ fst π-α' y
    forward∘backward-on-π y =
      forward-fun (backward-fun (fst π-α' y))
        ≡⟨ cong forward-fun (cong (λ h → fst h y) backward-eval) ⟩
      forward-fun (fst backward-composite y)
        ≡⟨ refl ⟩  -- backward-composite = π-α ∘ equiv⁻¹-hom
      forward-fun (fst π-α (fst equiv⁻¹-hom y))
        ≡⟨ cong (λ h → fst h (fst equiv⁻¹-hom y)) forward-eval ⟩
      fst composite-hom (fst equiv⁻¹-hom y)
        ≡⟨ refl ⟩  -- composite-hom = π-α' ∘ embBR-hom
      fst π-α' (embBR (fst equiv⁻¹-hom y))
        ≡⟨ cong (fst π-α') (embBR∘equiv⁻¹≡id y) ⟩
      fst π-α' y ∎

    forward∘backward-ext : (forward-fun ∘ backward-fun) ∘ fst π-α' ≡ (λ y → y) ∘ fst π-α'
    forward∘backward-ext = funExt forward∘backward-on-π

    forward∘backward : (y : ⟨ target ⟩) → forward-fun (backward-fun y) ≡ y
    forward∘backward = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ QB./Im f₀} {f = α'} (⟨ target ⟩ , target-isSet) forward∘backward-ext)

    step1-iso : Iso ⟨ source ⟩ ⟨ target ⟩
    Iso.fun step1-iso = forward-fun
    Iso.inv step1-iso = backward-fun
    Iso.sec step1-iso = forward∘backward
    Iso.ret step1-iso = backward∘forward

    step1-equiv-fun : ⟨ source ⟩ ≃ ⟨ target ⟩
    step1-equiv-fun = isoToEquiv step1-iso

    step1-equiv : BooleanRingEquiv (BoolBR QB./Im α) ((freeBA ℕ QB./Im f₀) QB./Im α')
    step1-equiv = step1-equiv-fun , snd forward-hom

    open IsCommRingHom

    embBR-pres0 : embBR false ≡ BooleanRingStr.𝟘 (snd (freeBA ℕ QB./Im f₀))
    embBR-pres0 = pres0 (snd equiv)

    embBR-pres1 : embBR true ≡ BooleanRingStr.𝟙 (snd (freeBA ℕ QB./Im f₀))
    embBR-pres1 = pres1 (snd equiv)

    π₀-pres0 : π₀ 𝟘 ≡ BooleanRingStr.𝟘 (snd (freeBA ℕ QB./Im f₀))
    π₀-pres0 = pres0 (snd QB.quotientImageHom)

    π₀-pres1 : π₀ 𝟙 ≡ BooleanRingStr.𝟙 (snd (freeBA ℕ QB./Im f₀))
    π₀-pres1 = pres1 (snd QB.quotientImageHom)

    α'≡π₀∘g-pointwise : (n : ℕ) → α' n ≡ π₀ (g n)
    α'≡π₀∘g-pointwise n with α n
    ... | true  = embBR-pres1 ∙ sym π₀-pres1   -- embBR true = 𝟙 = π₀ 𝟙
    ... | false = embBR-pres0 ∙ sym π₀-pres0   -- embBR false = 𝟘 = π₀ 𝟘

    α'≡π₀∘g : α' ≡ π₀ ∘ g
    α'≡π₀∘g = funExt α'≡π₀∘g-pointwise

    step1-equiv' : BooleanRingEquiv (BoolBR QB./Im α) ((freeBA ℕ QB./Im f₀) QB./Im (π₀ ∘ g))
    step1-equiv' = subst (λ f → BooleanRingEquiv (BoolBR QB./Im α) ((freeBA ℕ QB./Im f₀) QB./Im f)) α'≡π₀∘g step1-equiv

    A' : BooleanRing ℓ-zero
    A' = BoolBR QB./Im α

    B' : BooleanRing ℓ-zero
    B' = (freeBA ℕ QB./Im f₀) QB./Im (π₀ ∘ g)

    C' : BooleanRing ℓ-zero
    C' = freeBA ℕ QB./Im (⊎.rec f₀ g)

    D' : BooleanRing ℓ-zero
    D' = freeBA ℕ QB./Im h

    invStep2 : BooleanRingEquiv B' C'
    invStep2 = invBooleanRingEquiv (freeBA ℕ QB./Im (⊎.rec f₀ g)) ((freeBA ℕ QB./Im f₀) QB./Im (π₀ ∘ g)) step2-equiv

    invStep3 : BooleanRingEquiv C' D'
    invStep3 = invBooleanRingEquiv (freeBA ℕ QB./Im h) (freeBA ℕ QB./Im (⊎.rec f₀ g)) step3-equiv

    step12 : BooleanRingEquiv A' C'
    step12 = compBoolRingEquiv A' B' C' step1-equiv' invStep2

    equivToPresentation : BooleanRingEquiv (BoolBR QB./Im α) (freeBA ℕ QB./Im h)
    equivToPresentation = compBoolRingEquiv A' C' D' step12 invStep3

2/α-Booleω : (α : binarySequence) → Booleω
2/α-Booleω α = (BoolBR QB./Im α) , quotientPreservesBooleω α

mp-from-SD : StoneDualityAxiom → MarkovPrinciple
mp-from-SD SD α α≠0 = MarkovLib.extract' α (MarkovLib.∃αn α true-in-ideal)
  where
  open import Axioms.StoneDuality using (evaluationMap)
  open import CommRingQuotients.TrivialIdeal using (trivialQuotient→1∈I)
  import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ

  BoolCR = BooleanRing→CommRing BoolBR
  αIdeal = IQ.genIdeal BoolCR α

  sp-empty : Sp (2/α-Booleω α) → ⊥
  sp-empty = MarkovLib.emptySp α α≠0

  0≡1-BR : BooleanRingStr.𝟘 (snd (BoolBR QB./Im α)) ≡ BooleanRingStr.𝟙 (snd (BoolBR QB./Im α))
  0≡1-BR = SpectrumEmptyImpliesTrivial.0≡1-in-B SD (2/α-Booleω α) sp-empty

  open import QuotientBool using (_/Im_; quotientPreservesIdem)
  opaque
    unfolding _/Im_
    0≡1-CR : CommRingStr.0r (snd (BoolCR IQ./Im α)) ≡ CommRingStr.1r (snd (BoolCR IQ./Im α))
    0≡1-CR = 0≡1-BR

  1≡0-CR : CommRingStr.1r (snd (BoolCR IQ./Im α)) ≡ CommRingStr.0r (snd (BoolCR IQ./Im α))
  1≡0-CR = sym 0≡1-CR

  true-in-αIdeal : true ∈ fst αIdeal
  true-in-αIdeal = trivialQuotient→1∈I BoolCR αIdeal 1≡0-CR

  true-in-ideal : IQ.generatedIdeal BoolCR α true
  true-in-ideal = true-in-αIdeal

quotient-Booleω : binarySequence → Booleω
quotient-Booleω α = BoolBR QB./Im α , quotientPreservesBooleω α

postulate
  sd-axiom : StoneDualityAxiom

-- SurjectionsAreFormalSurjections axiom (tex line 294-297)

isInjectiveBoolHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isInjectiveBoolHom B C g = (x y : ⟨ fst B ⟩) → fst g x ≡ fst g y → x ≡ y

Sp-hom : (B C : Booleω) → BoolHom (fst B) (fst C) → Sp C → Sp B
Sp-hom B C g h = h ∘cr g

isSurjectiveSpHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isSurjectiveSpHom B C g = (h : Sp B) → ∥ Σ[ h' ∈ Sp C ] Sp-hom B C g h' ≡ h ∥₁

SurjectionsAreFormalSurjectionsAxiom : Type (ℓ-suc ℓ-zero)
SurjectionsAreFormalSurjectionsAxiom = (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isInjectiveBoolHom B C g ↔ isSurjectiveSpHom B C g

postulate
  surj-formal-axiom : SurjectionsAreFormalSurjectionsAxiom

injective→Sp-surjective : (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isInjectiveBoolHom B C g → isSurjectiveSpHom B C g
injective→Sp-surjective B C g = fst (surj-formal-axiom B C g)

Sp-surjective→injective : (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isSurjectiveSpHom B C g → isInjectiveBoolHom B C g
Sp-surjective→injective B C g = snd (surj-formal-axiom B C g)

-- Local Choice axiom (tex line 348-353, AxLocalChoice)

SpTypeFamily : Booleω → Type (ℓ-suc ℓ-zero)
SpTypeFamily B = Sp B → Type ℓ-zero

isSurjectiveSpMap : {B C : Booleω} → (Sp C → Sp B) → Type ℓ-zero
isSurjectiveSpMap {B} {C} q = (h : Sp B) → ∥ Σ[ h' ∈ Sp C ] q h' ≡ h ∥₁

LocalChoiceAxiom : Type (ℓ-suc ℓ-zero)
LocalChoiceAxiom = (B : Booleω) (P : SpTypeFamily B)
  → ((s : Sp B) → ∥ P s ∥₁)
  → ∥ Σ[ C ∈ Booleω ] Σ[ q ∈ (Sp C → Sp B) ]
      (isSurjectiveSpMap {B} {C} q × ((t : Sp C) → P (q t))) ∥₁

postulate
  localChoice-axiom : LocalChoiceAxiom

-- Dependent Choice axiom (tex line 324, AxDependentChoice)

SeqLimit : (E : ℕ → Type ℓ-zero) → ((n : ℕ) → E (suc n) → E n) → Type ℓ-zero
SeqLimit E p = Σ[ f ∈ ((n : ℕ) → E n) ] ((n : ℕ) → p n (f (suc n)) ≡ f n)

seqLim-proj₀ : (E : ℕ → Type ℓ-zero) (p : (n : ℕ) → E (suc n) → E n)
             → SeqLimit E p → E 0
seqLim-proj₀ E p (f , _) = f 0

DependentChoiceAxiom : Type (ℓ-suc ℓ-zero)
DependentChoiceAxiom = (E : ℕ → Type ℓ-zero) (p : (n : ℕ) → E (suc n) → E n)
  → ((n : ℕ) → (y : E n) → ∥ Σ[ x ∈ E (suc n) ] p n x ≡ y ∥₁)  -- each p_n surjective
  → (e₀ : E 0) → ∥ Σ[ s ∈ SeqLimit E p ] seqLim-proj₀ E p s ≡ e₀ ∥₁

postulate
  dependentChoice-axiom : DependentChoiceAxiom

CountableChoiceAxiom : Type (ℓ-suc ℓ-zero)
CountableChoiceAxiom = (A : ℕ → Type ℓ-zero)
  → ((n : ℕ) → ∥ A n ∥₁)
  → ∥ ((n : ℕ) → A n) ∥₁

countableChoice : CountableChoiceAxiom
countableChoice A witnesses = PT.map extract seqLim-exists
  where
  E : ℕ → Type ℓ-zero
  E zero = Unit
  E (suc n) = E n × A n

  p : (n : ℕ) → E (suc n) → E n
  p n (e , _) = e

  p-surj : (n : ℕ) → (y : E n) → ∥ Σ[ x ∈ E (suc n) ] p n x ≡ y ∥₁
  p-surj n y = PT.map (λ a → (y , a) , refl) (witnesses n)

  e₀ : E 0
  e₀ = tt

  seqLim-exists : ∥ Σ[ s ∈ SeqLimit E p ] seqLim-proj₀ E p s ≡ e₀ ∥₁
  seqLim-exists = dependentChoice-axiom E p p-surj e₀

  extractAt : SeqLimit E p → (n : ℕ) → A n
  extractAt (f , coh) n = snd (f (suc n))

  extract : Σ[ s ∈ SeqLimit E p ] seqLim-proj₀ E p s ≡ e₀ → (n : ℕ) → A n
  extract (s , _) = extractAt s

mp : MarkovPrinciple
mp = mp-from-SD sd-axiom

¬-Closed : Closed → Open
¬-Closed C = ¬hProp (fst C) , negClosedIsOpen mp (fst C) (snd C)

openOr : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
       → isOpenProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
openOr = openOrMP mp

∞ : ℕ∞
∞ = (λ _ → false) , (λ m n αm=t _ → ex-falso (false≢true αm=t))

ι : ℕ → ℕ∞
ι n = α , atMostOnce
  where
  α : binarySequence
  α m with discreteℕ m n
  ... | yes _ = true
  ... | no _ = false

  atMostOnce : hitsAtMostOnce α
  atMostOnce m k αm=t αk=t with discreteℕ m n | discreteℕ k n
  ... | yes m=n | yes k=n = m=n ∙ sym k=n
  ... | yes _ | no k≠n = ex-falso (false≢true αk=t)
  ... | no m≠n | yes _ = ex-falso (false≢true αm=t)
  ... | no m≠n | no k≠n = ex-falso (false≢true αm=t)

ι-at-n : (n : ℕ) → fst (ι n) n ≡ true
ι-at-n n with discreteℕ n n
... | yes _ = refl
... | no n≠n = ex-falso (n≠n refl)

ι-at-m≠n : (n m : ℕ) → ¬ (m ≡ n) → fst (ι n) m ≡ false
ι-at-m≠n n m m≠n with discreteℕ m n
... | yes m=n = ex-falso (m≠n m=n)
... | no _ = refl

ι≠∞ : (n : ℕ) → ¬ (ι n ≡ ∞)
ι≠∞ n ι=∞ = false≢true (sym (cong (λ x → fst x n) ι=∞) ∙ ι-at-n n)

ι-injective : (m n : ℕ) → ι m ≡ ι n → m ≡ n
ι-injective m n ιm=ιn =
  let ιm-at-m : fst (ι m) m ≡ true
      ιm-at-m = ι-at-n m
      ιn-at-m : fst (ι n) m ≡ true
      ιn-at-m = cong (λ x → fst x m) (sym ιm=ιn) ∙ ιm-at-m
  in snd (ι n) m n ιn-at-m (ι-at-n n)

-- Markov principle for ℕ∞ elements (tex Theorem after NotWLPO, line 500)
ℕ∞-Markov : (α : ℕ∞) → ¬ ((n : ℕ) → fst α n ≡ false) → Σ[ n ∈ ℕ ] fst α n ≡ true
ℕ∞-Markov α = mp (fst α)

ℕ∞-notInfty→witness : (α : ℕ∞) → ¬ (α ≡ ∞) → Σ[ n ∈ ℕ ] fst α n ≡ true
ℕ∞-notInfty→witness α α≠∞ = ℕ∞-Markov α ¬all-false
  where
  ¬all-false : ¬ ((n : ℕ) → fst α n ≡ false)
  ¬all-false all-false = α≠∞ (Σ≡Prop isPropHitsAtMostOnce (funExt all-false))

witness→ℕ∞-notInfty : (α : ℕ∞) → Σ[ n ∈ ℕ ] fst α n ≡ true → ¬ (α ≡ ∞)
witness→ℕ∞-notInfty α (n , αn=t) α=∞ = false≢true (sym (cong (λ x → fst x n) α=∞) ∙ αn=t)

ℕ∞-witness-unique : (α : ℕ∞) → (n m : ℕ) → fst α n ≡ true → fst α m ≡ true → n ≡ m
ℕ∞-witness-unique α n m αn=t αm=t = snd α n m αn=t αm=t

∞-char : (α : ℕ∞) → (α ≡ ∞) ↔ ((n : ℕ) → fst α n ≡ false)
∞-char α = forward , backward
  where
  forward : α ≡ ∞ → (n : ℕ) → fst α n ≡ false
  forward α=∞ n = cong (λ x → fst x n) α=∞

  backward : ((n : ℕ) → fst α n ≡ false) → α ≡ ∞
  backward all-false = Σ≡Prop isPropHitsAtMostOnce (funExt all-false)

ℕ∞-witness→ι : (α : ℕ∞) → (n : ℕ) → fst α n ≡ true → α ≡ ι n
ℕ∞-witness→ι α n αn=t = Σ≡Prop isPropHitsAtMostOnce (funExt lemma)
  where
  lemma : (m : ℕ) → fst α m ≡ fst (ι n) m
  lemma m with discreteℕ m n
  lemma m | yes m=n = cong (fst α) m=n ∙ αn=t  -- fst (ι n) m = true
  lemma m | no m≠n = helper (fst α m) refl  -- fst (ι n) m = false here
    where
    helper : (b : Bool) → fst α m ≡ b → fst α m ≡ false
    helper false αm=f = αm=f
    helper true αm=t = ex-falso (m≠n (snd α m n αm=t αn=t))

ℕ∞-equality-closed : (α β : ℕ∞) → isClosedProp ((α ≡ β) , isSetΣSndProp (isSetΠ (λ _ → isSetBool)) isPropHitsAtMostOnce α β)
ℕ∞-equality-closed α β = γ , forward , backward
  where
  γ : binarySequence
  γ n with fst α n =B fst β n
  ... | yes _ = false
  ... | no _ = true

  forward : α ≡ β → (n : ℕ) → γ n ≡ false
  forward α=β n with fst α n =B fst β n
  ... | yes _ = refl
  ... | no αn≠βn = ex-falso (αn≠βn (cong (λ x → fst x n) α=β))

  backward : ((n : ℕ) → γ n ≡ false) → α ≡ β
  backward all-false = Σ≡Prop isPropHitsAtMostOnce (funExt pointwise)
    where
    pointwise : (n : ℕ) → fst α n ≡ fst β n
    pointwise n with fst α n =B fst β n | all-false n
    ... | yes αn=βn | _ = αn=βn
    ... | no αn≠βn | γn=f = ex-falso (true≢false γn=f)

postulate
  llpo : LLPO

data Reveal_·_is_ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) (y : B x) : Type₀ where
  [_] : f x ≡ y → Reveal f · x is y

inspect : ∀ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) → Reveal f · x is (f x)
inspect f x = [ refl ]

triangular : ℕ → ℕ
triangular zero = zero
triangular (suc n) = suc n +ℕ triangular n

cantorPair : ℕ → ℕ → ℕ
cantorPair m n = triangular (m +ℕ n) +ℕ n

_<ᵇ'_ : ℕ → ℕ → Bool
zero <ᵇ' zero = false
zero <ᵇ' suc n = true
suc m <ᵇ' zero = false
suc m <ᵇ' suc n = m <ᵇ' n

findDiagonal : ℕ → ℕ → ℕ → ℕ
findDiagonal zero k diag = diag  -- out of fuel, return current
findDiagonal (suc fuel) k diag =
  if k <ᵇ' triangular (suc diag)
  then diag  -- k < triangular(diag+1), so k is on diagonal diag
  else findDiagonal fuel k (suc diag)  -- k >= triangular(diag+1), try next

cantorUnpair : ℕ → ℕ × ℕ
cantorUnpair k =
  let w = findDiagonal (suc k) k 0  -- use k+1 as fuel (sufficient)
      n = k ∸ triangular w
      m = w ∸ n
  in (m , n)

<ᵇ'-reflects : (m n : ℕ) → m <ᵇ' n ≡ true → m < n
<ᵇ'-reflects zero zero p = ex-falso (false≢true p)
<ᵇ'-reflects zero (suc n) _ = suc-≤-suc zero-≤
<ᵇ'-reflects (suc m) zero p = ex-falso (false≢true p)
<ᵇ'-reflects (suc m) (suc n) p = suc-≤-suc (<ᵇ'-reflects m n p)

¬<ᵇ'-reflects : (m n : ℕ) → m <ᵇ' n ≡ false → n ≤ m
¬<ᵇ'-reflects zero zero _ = ≤-refl
¬<ᵇ'-reflects zero (suc n) p = ex-falso (true≢false p)
¬<ᵇ'-reflects (suc m) zero _ = zero-≤
¬<ᵇ'-reflects (suc m) (suc n) p = suc-≤-suc (¬<ᵇ'-reflects m n p)

+-∸-assoc : (a b c : ℕ) → c ≤ b → a +ℕ b ∸ c ≡ a +ℕ (b ∸ c)
+-∸-assoc a zero zero _ = refl
+-∸-assoc a zero (suc c) sc≤0 = ex-falso (¬-<-zero sc≤0)
+-∸-assoc a (suc b) zero _ = refl
+-∸-assoc a (suc b) (suc c) sc≤sb =
  a +ℕ suc b ∸ suc c   ≡⟨ cong (_∸ suc c) (+-suc a b) ⟩
  suc (a +ℕ b) ∸ suc c ≡⟨ refl ⟩
  a +ℕ b ∸ c           ≡⟨ +-∸-assoc a b c (pred-≤-pred sc≤sb) ⟩
  a +ℕ (b ∸ c)         ∎

∸+-cancel : (a b : ℕ) → b ≤ a → (a ∸ b) +ℕ b ≡ a
∸+-cancel a zero _ = +-zero a
∸+-cancel zero (suc b) sb≤0 = ex-falso (¬-<-zero sb≤0)
∸+-cancel (suc a) (suc b) sb≤sa =
  (suc a ∸ suc b) +ℕ suc b   ≡⟨ refl ⟩
  (a ∸ b) +ℕ suc b           ≡⟨ +-suc (a ∸ b) b ⟩
  suc ((a ∸ b) +ℕ b)         ≡⟨ cong suc (∸+-cancel a b (pred-≤-pred sb≤sa)) ⟩
  suc a ∎

triangular≤cantorPair : (m n : ℕ) → triangular (m +ℕ n) ≤ cantorPair m n
triangular≤cantorPair m n = ≤-+k-local (triangular (m +ℕ n)) n
  where
  ≤-+k-local : (a b : ℕ) → a ≤ a +ℕ b
  ≤-+k-local a zero = subst (a ≤_) (sym (+-zero a)) ≤-refl
  ≤-+k-local a (suc b) =
    let step1 : a ≤ a +ℕ b
        step1 = ≤-+k-local a b
        step2 : a ≤ suc (a +ℕ b)
        step2 = ≤-suc step1
    in subst (a ≤_) (sym (+-suc a b)) step2

cantorPair<triangular-suc : (m n : ℕ) → cantorPair m n < triangular (suc (m +ℕ n))
cantorPair<triangular-suc m n = goal
  where
  w = m +ℕ n

  n≤w : n ≤ w
  n≤w = n≤m+n-local m n
    where
    n≤m+n-local : (a b : ℕ) → b ≤ a +ℕ b
    n≤m+n-local zero b = ≤-refl
    n≤m+n-local (suc a) b = ≤-trans (n≤m+n-local a b) ≤-sucℕ

  sucn≤sucw : suc n ≤ suc w
  sucn≤sucw = suc-≤-suc n≤w

  step1 : triangular w +ℕ suc n ≤ triangular w +ℕ suc w
  step1 = ≤-+k-mono (triangular w) (suc n) (suc w) sucn≤sucw
    where
    ≤-+k-mono : (a b c : ℕ) → b ≤ c → a +ℕ b ≤ a +ℕ c
    ≤-+k-mono zero b c b≤c = b≤c
    ≤-+k-mono (suc a) b c b≤c = suc-≤-suc (≤-+k-mono a b c b≤c)

  eq1 : suc (triangular w +ℕ n) ≡ triangular w +ℕ suc n
  eq1 = sym (+-suc (triangular w) n)

  eq2 : triangular w +ℕ suc w ≡ suc w +ℕ triangular w
  eq2 = +-comm (triangular w) (suc w)

  eq3 : suc w +ℕ triangular w ≡ triangular (suc w)
  eq3 = refl

  goal : suc (triangular w +ℕ n) ≤ triangular (suc w)
  goal = subst (_≤ triangular (suc w)) (sym eq1)
           (subst (triangular w +ℕ suc n ≤_) (eq2 ∙ eq3) step1)

findDiagonal-found : (fuel k diag : ℕ) → k <ᵇ' triangular (suc diag) ≡ true
                   → findDiagonal (suc fuel) k diag ≡ diag
findDiagonal-found fuel k diag p with k <ᵇ' triangular (suc diag) | p
... | true | _ = refl
... | false | q = ex-falso (false≢true q)

findDiagonal-continue : (fuel k diag : ℕ) → k <ᵇ' triangular (suc diag) ≡ false
                      → findDiagonal (suc fuel) k diag ≡ findDiagonal fuel k (suc diag)
findDiagonal-continue fuel k diag p with k <ᵇ' triangular (suc diag) | p
... | false | _ = refl
... | true | q = ex-falso (true≢false q)

<ᵇ'-suc : (n : ℕ) → n <ᵇ' suc n ≡ true
<ᵇ'-suc zero = refl
<ᵇ'-suc (suc n) = <ᵇ'-suc n

<-reflects-<ᵇ' : (a b : ℕ) → a < b → a <ᵇ' b ≡ true
<-reflects-<ᵇ' zero zero 1≤0 = ex-falso (¬-<-zero 1≤0)
<-reflects-<ᵇ' zero (suc b) _ = refl
<-reflects-<ᵇ' (suc a) zero sa<0 = ex-falso (¬-<-zero sa<0)
<-reflects-<ᵇ' (suc a) (suc b) sa<sb = <-reflects-<ᵇ' a b (pred-≤-pred sa<sb)

cantorPair<ᵇ'-triangular-suc : (m n : ℕ) → cantorPair m n <ᵇ' triangular (suc (m +ℕ n)) ≡ true
cantorPair<ᵇ'-triangular-suc m n = <-reflects-<ᵇ' _ _ (cantorPair<triangular-suc m n)

cantorPair-triangular-diff : (m n : ℕ) → cantorPair m n ∸ triangular (m +ℕ n) ≡ n
cantorPair-triangular-diff m n = +∸-cancel' n (triangular (m +ℕ n))
  where
  +∸-cancel' : (a b : ℕ) → (b +ℕ a) ∸ b ≡ a
  +∸-cancel' a zero = refl
  +∸-cancel' a (suc b) = +∸-cancel' a b

m+n∸n≡m : (m n : ℕ) → (m +ℕ n) ∸ n ≡ m
m+n∸n≡m = +∸

triangular-suc : (n : ℕ) → triangular n < triangular (suc n)
triangular-suc n = ≤-+k-mono-l 1 (suc n) (triangular n) (suc-≤-suc zero-≤)
  where
  ≤-+k-mono-l : (a b c : ℕ) → a ≤ b → a +ℕ c ≤ b +ℕ c
  ≤-+k-mono-l zero b c _ = ≤-+k-r b c
    where
    ≤-+k-r : (x y : ℕ) → y ≤ x +ℕ y
    ≤-+k-r zero y = ≤-refl
    ≤-+k-r (suc x) y = ≤-trans (≤-+k-r x y) ≤-sucℕ
  ≤-+k-mono-l (suc a) zero c sa≤0 = ex-falso (¬-<-zero sa≤0)
  ≤-+k-mono-l (suc a) (suc b) c sa≤sb = suc-≤-suc (≤-+k-mono-l a b c (pred-≤-pred sa≤sb))

triangular-mono-< : (n m : ℕ) → n < m → triangular n < triangular m
triangular-mono-< n zero n<0 = ex-falso (¬-<-zero n<0)
triangular-mono-< n (suc m) sn≤sm with n ≟ m
... | lt n<m = <-trans (triangular-mono-< n m n<m) (triangular-suc m)
... | eq n≡m = subst (λ x → triangular x < triangular (suc m)) (sym n≡m) (triangular-suc m)
... | gt m<n = ex-falso (¬m<m (≤-trans m<n (pred-≤-pred sn≤sm)))

triangular-mono-≤ : (n m : ℕ) → n ≤ m → triangular n ≤ triangular m
triangular-mono-≤ n m n≤m with n ≟ m
... | lt n<m = <-weaken (triangular-mono-< n m n<m)
... | eq n≡m = subst (λ x → triangular n ≤ triangular x) n≡m ≤-refl
... | gt m<n = ex-falso (¬m<m (≤-trans m<n n≤m))

k≥triangular-suc-acc : (k w acc : ℕ) → acc < w → triangular w ≤ k
                     → triangular (suc acc) ≤ k
k≥triangular-suc-acc k w acc acc<w Tw≤k =
  ≤-trans (triangular-mono-≤ (suc acc) w acc<w) Tw≤k

k≮ᵇ'triangular-suc-acc : (k w acc : ℕ) → acc < w → triangular w ≤ k
                      → k <ᵇ' triangular (suc acc) ≡ false
k≮ᵇ'triangular-suc-acc k w acc acc<w Tw≤k = ≤-reflects-¬<ᵇ' _ _ (k≥triangular-suc-acc k w acc acc<w Tw≤k)
  where
  ≤-reflects-¬<ᵇ' : (a b : ℕ) → b ≤ a → a <ᵇ' b ≡ false
  ≤-reflects-¬<ᵇ' zero zero _ = refl
  ≤-reflects-¬<ᵇ' (suc a) zero _ = refl
  ≤-reflects-¬<ᵇ' zero (suc b) sb≤0 = ex-falso (¬-<-zero sb≤0)
  ≤-reflects-¬<ᵇ' (suc a) (suc b) sb≤sa = ≤-reflects-¬<ᵇ' a b (pred-≤-pred sb≤sa)

findDiagonal-aux : (w k acc fuel : ℕ) → w ∸ acc ≤ fuel
                 → k <ᵇ' triangular (suc w) ≡ true
                 → triangular w ≤ k
                 → acc ≤ w
                 → findDiagonal (suc fuel) k acc ≡ w
findDiagonal-aux w k acc zero w∸acc≤0 k<Tsw Tw≤k acc≤w with w ≟ acc
... | lt w<acc = ex-falso (¬m<m (≤-trans w<acc acc≤w))
... | eq w≡acc = subst (findDiagonal 1 k acc ≡_) (sym w≡acc) (findDiagonal-found 0 k acc (subst (λ x → k <ᵇ' triangular (suc x) ≡ true) w≡acc k<Tsw))
... | gt acc<w = ex-falso (¬m<m (≤-trans (∸-<-from w acc acc<w) w∸acc≤0))
  where
  ∸-<-from : (a b : ℕ) → b < a → 1 ≤ a ∸ b
  ∸-<-from zero zero 1≤0 = ex-falso (¬-<-zero 1≤0)
  ∸-<-from zero (suc b) sb<0 = ex-falso (¬-<-zero sb<0)
  ∸-<-from (suc a) zero _ = suc-≤-suc zero-≤
  ∸-<-from (suc a) (suc b) sb<sa = ∸-<-from a b (pred-≤-pred sb<sa)

findDiagonal-aux w k acc (suc fuel) w∸acc≤sf k<Tsw Tw≤k acc≤w with w ≟ acc
... | lt w<acc = ex-falso (¬m<m (≤-trans w<acc acc≤w))
... | eq w≡acc = subst (findDiagonal (suc (suc fuel)) k acc ≡_) (sym w≡acc) (findDiagonal-found (suc fuel) k acc (subst (λ x → k <ᵇ' triangular (suc x) ≡ true) w≡acc k<Tsw))
... | gt acc<w =
  let step1 = findDiagonal-continue (suc fuel) k acc (k≮ᵇ'triangular-suc-acc k w acc acc<w Tw≤k)
      step2 = findDiagonal-aux w k (suc acc) fuel (≤-pred-∸' w acc acc<w w∸acc≤sf) k<Tsw Tw≤k acc<w
  in step1 ∙ step2
  where
  ≤-pred-∸' : (w acc : ℕ) → acc < w → w ∸ acc ≤ suc fuel → w ∸ suc acc ≤ fuel
  ≤-pred-∸' zero acc 0<acc _ = ex-falso (¬-<-zero 0<acc)
  ≤-pred-∸' (suc w') acc acc<sw w∸acc≤sf = ≤-pred-∸-aux w' acc acc<sw w∸acc≤sf
    where
    ≤-pred-∸-aux : (w acc : ℕ) → acc < suc w → suc w ∸ acc ≤ suc fuel → suc w ∸ suc acc ≤ fuel
    ≤-pred-∸-aux w zero _ sw∸0≤sf = pred-≤-pred sw∸0≤sf
    ≤-pred-∸-aux w (suc acc) sacc<sw p = ≤-pred-∸-aux' w acc (pred-≤-pred sacc<sw) p
      where
      ≤-pred-∸-aux' : (w acc : ℕ) → acc < w → w ∸ acc ≤ suc fuel → w ∸ suc acc ≤ fuel
      ≤-pred-∸-aux' zero acc 1≤0 _ = ex-falso (¬-<-zero 1≤0)
      ≤-pred-∸-aux' (suc w') acc acc<sw' w∸acc≤sf' = ≤-pred-∸-aux w' acc acc<sw' w∸acc≤sf'

w≤triangular : (w : ℕ) → w ≤ triangular w +ℕ w
w≤triangular w = ≤-+k-r' w (triangular w)
  where
  ≤-+k-r' : (n m : ℕ) → n ≤ m +ℕ n
  ≤-+k-r' n zero = ≤-refl
  ≤-+k-r' n (suc m) = ≤-trans (≤-+k-r' n m) ≤-sucℕ

w≤cantorPair : (m n : ℕ) → m +ℕ n ≤ cantorPair m n
w≤cantorPair m n = ≤-trans (m+n≤tri-m+n m n) (≤-+k-r (triangular (m +ℕ n)) n)
  where
  n≤triangular-n : (n : ℕ) → n ≤ triangular n
  n≤triangular-n zero = zero-≤
  n≤triangular-n (suc n) = suc-≤-suc (≤-trans (n≤triangular-n n) (≤-+k-r' (triangular n) n))
    where
    ≤-+k-r' : (a b : ℕ) → a ≤ b +ℕ a
    ≤-+k-r' a zero = ≤-refl
    ≤-+k-r' a (suc b) = ≤-trans (≤-+k-r' a b) ≤-sucℕ

  m+n≤tri-m+n : (m n : ℕ) → m +ℕ n ≤ triangular (m +ℕ n)
  m+n≤tri-m+n m n = n≤triangular-n (m +ℕ n)

  ≤-+k-r : (a b : ℕ) → a ≤ a +ℕ b
  ≤-+k-r a zero = subst (a ≤_) (sym (+-zero a)) ≤-refl
  ≤-+k-r a (suc b) = subst (a ≤_) (sym (+-suc a b)) (≤-trans (≤-+k-r a b) ≤-sucℕ)

findDiagonal-correct : (m n : ℕ) →
  findDiagonal (suc (cantorPair m n)) (cantorPair m n) 0 ≡ m +ℕ n
findDiagonal-correct m n =
  let k = cantorPair m n
      w = m +ℕ n
  in findDiagonal-aux w k 0 k
       (w≤cantorPair m n)
       (cantorPair<ᵇ'-triangular-suc m n)
       (triangular≤cantorPair m n)
       zero-≤

cantorUnpair-pair : (m n : ℕ) → cantorUnpair (cantorPair m n) ≡ (m , n)
cantorUnpair-pair m n =
  let k = cantorPair m n
      w = m +ℕ n
      findW = findDiagonal-correct m n
  in
  cantorUnpair k                                         ≡⟨ refl ⟩
  (let w' = findDiagonal (suc k) k 0
       n' = k ∸ triangular w'
       m' = w' ∸ n'
   in (m' , n'))                                          ≡⟨ cong (λ w' → ((w' ∸ (k ∸ triangular w')) , (k ∸ triangular w'))) findW ⟩
  (w ∸ (k ∸ triangular w) , k ∸ triangular w)             ≡⟨ cong (λ x → (w ∸ x , x)) (cantorPair-triangular-diff m n) ⟩
  (w ∸ n , n)                                              ≡⟨ cong (λ x → (x , n)) (m+n∸n≡m m n) ⟩
  (m , n) ∎

openAnd : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
        → isOpenProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
openAnd P Q (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) = γ , forward , backward
  where
  γ : binarySequence
  γ k = let (n , m) = cantorUnpair k in α n and β m

  forward : ⟨ P ⟩ × ⟨ Q ⟩ → Σ[ k ∈ ℕ ] γ k ≡ true
  forward (p , q) =
    let (n , αn=t) = P→∃α p
        (m , βm=t) = Q→∃β q
        k = cantorPair n m
        γk=t : γ k ≡ true
        γk=t =
          γ k
            ≡⟨ cong (λ p → α (fst p) and β (snd p)) (cantorUnpair-pair n m) ⟩
          α n and β m
            ≡⟨ cong (λ x → x and β m) αn=t ⟩
          true and β m
            ≡⟨ cong (true and_) βm=t ⟩
          true ∎
    in (k , γk=t)

  backward : Σ[ k ∈ ℕ ] γ k ≡ true → ⟨ P ⟩ × ⟨ Q ⟩
  backward (k , γk=t) =
    let (n , m) = cantorUnpair k
        αn∧βm=t : α n and β m ≡ true
        αn∧βm=t = γk=t
        αn=t : α n ≡ true
        αn=t = and-true-left (α n) (β m) αn∧βm=t
        βm=t : β m ≡ true
        βm=t = and-true-right (α n) (β m) αn∧βm=t
    in (∃α→P (n , αn=t)) , (∃β→Q (m , βm=t))
    where
    and-true-left : (a b : Bool) → a and b ≡ true → a ≡ true
    and-true-left true true _ = refl
    and-true-left true false p = ex-falso (false≢true p)
    and-true-left false true p = ex-falso (false≢true p)
    and-true-left false false p = ex-falso (false≢true p)

    and-true-right : (a b : Bool) → a and b ≡ true → b ≡ true
    and-true-right true true _ = refl
    and-true-right true false p = ex-falso (false≢true p)
    and-true-right false true p = ex-falso (false≢true p)
    and-true-right false false p = ex-falso (false≢true p)

_∧-Open_ : Open → Open → Open
O₁ ∧-Open O₂ = ((⟨ fst O₁ ⟩ × ⟨ fst O₂ ⟩) , isProp× (snd (fst O₁)) (snd (fst O₂))) ,
               openAnd (fst O₁) (fst O₂) (snd O₁) (snd O₂)

_∧-Closed_ : Closed → Closed → Closed
C₁ ∧-Closed C₂ = ((⟨ fst C₁ ⟩ × ⟨ fst C₂ ⟩) , isProp× (snd (fst C₁)) (snd (fst C₂))) ,
                 closedAnd (fst C₁) (fst C₂) (snd C₁) (snd C₂)

firstTrue : binarySequence → binarySequence
firstTrue α zero = α zero
firstTrue α (suc n) with α zero
... | true = false
... | false = firstTrue (α ∘ suc) n

firstTrue-preserves-allFalse : (α : binarySequence) → ((n : ℕ) → α n ≡ false)
                             → (n : ℕ) → firstTrue α n ≡ false
firstTrue-preserves-allFalse α allF zero = allF zero
firstTrue-preserves-allFalse α allF (suc n) with α zero | allF zero
... | true  | α0=f = ex-falso (false≢true (sym α0=f))
... | false | _    = firstTrue-preserves-allFalse (α ∘ suc) (allF ∘ suc) n

firstTrue-hitsAtMostOnce : (α : binarySequence) → hitsAtMostOnce (firstTrue α)
firstTrue-hitsAtMostOnce α m n ftm=t ftn=t = aux α m n ftm=t ftn=t
  where
  aux : (α : binarySequence) → (m n : ℕ) → firstTrue α m ≡ true → firstTrue α n ≡ true → m ≡ n
  aux α zero zero _ _ = refl
  aux α zero (suc n) ft0=t ft-sn=t with α zero
  aux α zero (suc n) ft0=t ft-sn=t | true = ex-falso (false≢true ft-sn=t)
  aux α zero (suc n) ft0=t ft-sn=t | false = ex-falso (false≢true ft0=t)
  aux α (suc m) zero ft-sm=t ft0=t with α zero
  aux α (suc m) zero ft-sm=t ft0=t | true = ex-falso (false≢true ft-sm=t)
  aux α (suc m) zero ft-sm=t ft0=t | false = ex-falso (false≢true ft0=t)
  aux α (suc m) (suc n) ft-sm=t ft-sn=t with α zero
  aux α (suc m) (suc n) ft-sm=t ft-sn=t | true = ex-falso (false≢true ft-sm=t)
  aux α (suc m) (suc n) ft-sm=t ft-sn=t | false = cong suc (aux (α ∘ suc) m n ft-sm=t ft-sn=t)

firstTrue-true-implies-original-true : (α : binarySequence) (n : ℕ)
                                      → firstTrue α n ≡ true → α n ≡ true
firstTrue-true-implies-original-true α zero ft0=t = ft0=t
firstTrue-true-implies-original-true α (suc n) ft-sn=t with α zero
... | true  = ex-falso (false≢true ft-sn=t)
... | false = firstTrue-true-implies-original-true (α ∘ suc) n ft-sn=t

private
  firstTrue-with : (α : binarySequence) (n : ℕ) (b : Bool)
                  → α zero ≡ b
                  → firstTrue α (suc n) ≡ (if b then false else firstTrue (α ∘ suc) n)
  firstTrue-with α n true  p with α zero
  ... | true = refl
  ... | false = ex-falso (true≢false (sym p))
  firstTrue-with α n false p with α zero
  ... | true = ex-falso (false≢true (sym p))
  ... | false = refl

firstTrue-false-but-original-true : (α : binarySequence) (n : ℕ)
                                   → firstTrue α n ≡ false → α n ≡ true
                                   → Σ[ m ∈ ℕ ] (suc m ≤ n) × (α m ≡ true)
firstTrue-false-but-original-true α zero ft0=f α0=t = ex-falso (true≢false (sym α0=t ∙ ft0=f))
firstTrue-false-but-original-true α (suc n) ft-sn=f α-sn=t with α zero =B true
... | yes α0=t = zero , suc-≤-suc zero-≤ , α0=t
... | no α0≠t =
  let α0=f = ¬true→false (α zero) α0≠t
      eq : firstTrue α (suc n) ≡ firstTrue (α ∘ suc) n
      eq = firstTrue-with α n false α0=f ∙ refl
      ft-sn=f' : firstTrue (α ∘ suc) n ≡ false
      ft-sn=f' = sym eq ∙ ft-sn=f
      (m , m<n , αsm=t) = firstTrue-false-but-original-true (α ∘ suc) n ft-sn=f' α-sn=t
  in suc m , suc-≤-suc m<n , αsm=t

closedDeMorgan : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
               → ¬ ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
closedDeMorgan P Q (α , P→∀α , ∀α→P) (β , Q→∀β , ∀β→Q) ¬¬P∧¬Q =
  let -- Interleave α and β, then apply firstTrue to get an ℕ∞ element
      δ₀ : binarySequence
      δ₀ = interleave α β

      δ : binarySequence
      δ = firstTrue δ₀

      δ-hamo : hitsAtMostOnce δ
      δ-hamo = firstTrue-hitsAtMostOnce δ₀

      δ∞ : ℕ∞
      δ∞ = δ , δ-hamo

      llpo-result : ((k : ℕ) → δ (2 ·ℕ k) ≡ false) ⊎ ((k : ℕ) → δ (suc (2 ·ℕ k)) ≡ false)
      llpo-result = llpo δ∞

  in helper llpo-result
  where

  module _ where
    open WF.WFI (<-wellfounded)

    ResultOdd : ℕ → Type₀
    ResultOdd n = interleave α β n ≡ true
                → ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false)
                → Σ[ m ∈ ℕ ] (isEvenB m ≡ false) × (β (half m) ≡ true)

    find-first-true-odd-step : (n : ℕ) → ((m : ℕ) → m < n → ResultOdd m) → ResultOdd n
    find-first-true-odd-step n rec δ₀-n=t allEvensF with firstTrue (interleave α β) n =B true
    ... | yes ft-n=t with isEvenB n =B true
    ...   | yes n-even =
            let k = half n
                2k=n : 2 ·ℕ k ≡ n
                2k=n = 2·half-even n n-even
            in ex-falso (true≢false (sym (subst (λ x → firstTrue (interleave α β) x ≡ true) (sym 2k=n) ft-n=t)
                                     ∙ allEvensF k))
    ...   | no n-odd =
            let j = half n
                m-odd-eq : isEvenB n ≡ false
                m-odd-eq = ¬true→false (isEvenB n) n-odd
                βj=t : β j ≡ true
                βj=t = sym (interleave-odd α β n m-odd-eq) ∙ δ₀-n=t
            in n , m-odd-eq , βj=t
    find-first-true-odd-step n rec δ₀-n=t allEvensF | no ft-n≠t =
      let ft-n=f = ¬true→false (firstTrue (interleave α β) n) ft-n≠t
          (m , m<n , δ₀-m=t) = firstTrue-false-but-original-true (interleave α β) n ft-n=f δ₀-n=t
      in rec m m<n δ₀-m=t allEvensF

    find-first-true-odd : (n : ℕ) → ResultOdd n
    find-first-true-odd = induction find-first-true-odd-step

  allEvensF-implies-P : ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false) → ⟨ P ⟩
  allEvensF-implies-P allEvensF = closedIsStable P (α , P→∀α , ∀α→P) ¬¬P
    where
    ¬¬P : ¬ ¬ ⟨ P ⟩
    ¬¬P ¬p =
      let -- From ¬P, get witness that α has a true
          (k , αk=t) = mp α (λ all-false → ¬p (∀α→P all-false))
          δ₀-2k=t : interleave α β (2 ·ℕ k) ≡ true
          δ₀-2k=t = interleave-2k α β k ∙ αk=t
          (m , m-odd , βj=t) = find-first-true-odd (2 ·ℕ k) δ₀-2k=t allEvensF
          j = half m
          ¬q : ¬ ⟨ Q ⟩
          ¬q q = false≢true (sym (Q→∀β q j) ∙ βj=t)
      in ¬¬P∧¬Q (¬p , ¬q)

  module _ where
    open WF.WFI (<-wellfounded)

    ResultEven : ℕ → Type₀
    ResultEven n = interleave α β n ≡ true
                 → ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false)
                 → Σ[ m ∈ ℕ ] (isEvenB m ≡ true) × (α (half m) ≡ true)

    find-first-true-even-step : (n : ℕ) → ((m : ℕ) → m < n → ResultEven m) → ResultEven n
    find-first-true-even-step n rec δ₀-n=t allOddsF with firstTrue (interleave α β) n =B true
    ... | yes ft-n=t with isEvenB n =B true
    ...   | yes n-even =
            let j = half n
                αj=t : α j ≡ true
                αj=t = sym (interleave-even α β n n-even) ∙ δ₀-n=t
            in n , n-even , αj=t
    ...   | no n-odd =
            let k = half n
                n-odd-eq : isEvenB n ≡ false
                n-odd-eq = ¬true→false (isEvenB n) n-odd
                2k+1=n : suc (2 ·ℕ k) ≡ n
                2k+1=n = suc-2·half-odd n n-odd-eq
            in ex-falso (true≢false (sym (subst (λ x → firstTrue (interleave α β) x ≡ true) (sym 2k+1=n) ft-n=t)
                                     ∙ allOddsF k))
    find-first-true-even-step n rec δ₀-n=t allOddsF | no ft-n≠t =
      let ft-n=f = ¬true→false (firstTrue (interleave α β) n) ft-n≠t
          (m , m<n , δ₀-m=t) = firstTrue-false-but-original-true (interleave α β) n ft-n=f δ₀-n=t
      in rec m m<n δ₀-m=t allOddsF

    find-first-true-even : (n : ℕ) → ResultEven n
    find-first-true-even = induction find-first-true-even-step

  allOddsF-implies-Q : ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false) → ⟨ Q ⟩
  allOddsF-implies-Q allOddsF = closedIsStable Q (β , Q→∀β , ∀β→Q) ¬¬Q
    where
    ¬¬Q : ¬ ¬ ⟨ Q ⟩
    ¬¬Q ¬q =
      let (k , βk=t) = mp β (λ all-false → ¬q (∀β→Q all-false))
          δ₀-odd-k=t : interleave α β (suc (2 ·ℕ k)) ≡ true
          δ₀-odd-k=t = interleave-2k+1 α β k ∙ βk=t
          (m , m-even , αj=t) = find-first-true-even (suc (2 ·ℕ k)) δ₀-odd-k=t allOddsF
          j = half m
          ¬p : ¬ ⟨ P ⟩
          ¬p p = false≢true (sym (P→∀α p j) ∙ αj=t)
      in ¬¬P∧¬Q (¬p , ¬q)

  helper : ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false)
         ⊎ ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false)
         → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
  helper (inl allEvensF) = ∣ inl (allEvensF-implies-P allEvensF) ∣₁
  helper (inr allOddsF) = ∣ inr (allOddsF-implies-Q allOddsF) ∣₁

closedOr : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
         → isClosedProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
closedOr P Q Pclosed Qclosed = γ , forward , backward
  where
  ¬P : hProp ℓ-zero
  ¬P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩

  ¬Q : hProp ℓ-zero
  ¬Q = (¬ ⟨ Q ⟩) , isProp¬ ⟨ Q ⟩

  ¬Popen : isOpenProp ¬P
  ¬Popen = negClosedIsOpen mp P Pclosed

  ¬Qopen : isOpenProp ¬Q
  ¬Qopen = negClosedIsOpen mp Q Qclosed

  ¬P∧¬Q : hProp ℓ-zero
  ¬P∧¬Q = ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) , isProp× (isProp¬ ⟨ P ⟩) (isProp¬ ⟨ Q ⟩)

  ¬P∧¬Qopen : isOpenProp ¬P∧¬Q
  ¬P∧¬Qopen = openAnd ¬P ¬Q ¬Popen ¬Qopen

  γ : binarySequence
  γ = fst ¬P∧¬Qopen

  forward : ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ → (n : ℕ) → γ n ≡ false
  forward P∨Q n with γ n =B true
  ... | yes γn=t = ex-falso (PT.rec isProp⊥ (helper γn=t) P∨Q)
    where
    helper : γ n ≡ true → ⟨ P ⟩ ⊎ ⟨ Q ⟩ → ⊥
    helper γn=t (inl p) = fst (snd (snd ¬P∧¬Qopen) (n , γn=t)) p
    helper γn=t (inr q) = snd (snd (snd ¬P∧¬Qopen) (n , γn=t)) q
  ... | no γn≠t = ¬true→false (γ n) γn≠t

  backward : ((n : ℕ) → γ n ≡ false) → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
  backward all-false =
    closedDeMorgan P Q Pclosed Qclosed ¬¬P∧¬Q
    where
    ¬¬P∧¬Q : ¬ ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩))
    ¬¬P∧¬Q (¬p , ¬q) =
      let (n , γn=t) = fst (snd ¬P∧¬Qopen) (¬p , ¬q)
      in false≢true (sym (all-false n) ∙ γn=t)

_∨-Open_ : Open → Open → Open
O₁ ∨-Open O₂ = ((∥ ⟨ fst O₁ ⟩ ⊎ ⟨ fst O₂ ⟩ ∥₁) , squash₁) ,
               openOr (fst O₁) (fst O₂) (snd O₁) (snd O₂)

_∨-Closed_ : Closed → Closed → Closed
C₁ ∨-Closed C₂ = ((∥ ⟨ fst C₁ ⟩ ⊎ ⟨ fst C₂ ⟩ ∥₁) , squash₁) ,
                 closedOr (fst C₁) (fst C₂) (snd C₁) (snd C₂)

-- (tex line 716)
openDeMorgan : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
             → (¬ (⟨ P ⟩ × ⟨ Q ⟩)) ↔ ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁
openDeMorgan P Q Popen Qopen = forward , backward
  where
  ¬Pclosed : isClosedProp (¬hProp P)
  ¬Pclosed = negOpenIsClosed P Popen

  ¬Qclosed : isClosedProp (¬hProp Q)
  ¬Qclosed = negOpenIsClosed Q Qopen

  forward : ¬ (⟨ P ⟩ × ⟨ Q ⟩) → ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁
  forward ¬P×Q = closedDeMorgan (¬hProp P) (¬hProp Q) ¬Pclosed ¬Qclosed ¬¬¬P×¬¬Q
    where
    Pstable : ¬ ¬ ⟨ P ⟩ → ⟨ P ⟩
    Pstable = openIsStable mp P Popen

    Qstable : ¬ ¬ ⟨ Q ⟩ → ⟨ Q ⟩
    Qstable = openIsStable mp Q Qopen

    ¬¬¬P×¬¬Q : ¬ ((¬ ¬ ⟨ P ⟩) × (¬ ¬ ⟨ Q ⟩))
    ¬¬¬P×¬¬Q (¬¬p , ¬¬q) = ¬P×Q (Pstable ¬¬p , Qstable ¬¬q)

  backward : ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁ → ¬ (⟨ P ⟩ × ⟨ Q ⟩)
  backward = PT.rec (isProp¬ _) λ
    { (inl ¬p) (p , _) → ¬p p
    ; (inr ¬q) (_ , q) → ¬q q
    }

flatten : (ℕ → binarySequence) → binarySequence
flatten αs k = let (m , n) = cantorUnpair k in αs m n

closedCountableIntersection : (P : ℕ → hProp ℓ-zero)
                            → ((n : ℕ) → isClosedProp (P n))
                            → isClosedProp (((n : ℕ) → ⟨ P n ⟩) , isPropΠ (λ n → snd (P n)))
closedCountableIntersection P αs = β , forward , backward
  where
  αP : ℕ → binarySequence
  αP n = fst (αs n)

  β : binarySequence
  β = flatten αP

  forward : ((n : ℕ) → ⟨ P n ⟩) → (k : ℕ) → β k ≡ false
  forward allP k =
    let (m , n) = cantorUnpair k
        Pm→allFalse = fst (snd (αs m))
    in Pm→allFalse (allP m) n

  backward : ((k : ℕ) → β k ≡ false) → (n : ℕ) → ⟨ P n ⟩
  backward allβFalse n = allFalse→Pn allαnFalse
    where
    allFalse→Pn : ((k : ℕ) → αP n k ≡ false) → ⟨ P n ⟩
    allFalse→Pn = snd (snd (αs n))
    allαnFalse : (k : ℕ) → αP n k ≡ false
    allαnFalse k =
      αP n k
        ≡⟨ cong (λ p → αP (fst p) (snd p)) (sym (cantorUnpair-pair n k)) ⟩
      αP (fst (cantorUnpair (cantorPair n k))) (snd (cantorUnpair (cantorPair n k)))
        ≡⟨ allβFalse (cantorPair n k) ⟩
      false ∎

openCountableUnion : (P : ℕ → hProp ℓ-zero)
                   → ((n : ℕ) → isOpenProp (P n))
                   → isOpenProp (∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁ , squash₁)
openCountableUnion P αs = β , forward , backward
  where
  αP : ℕ → binarySequence
  αP n = fst (αs n)

  β : binarySequence
  β = flatten αP

  backward : Σ[ k ∈ ℕ ] β k ≡ true → ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁
  backward (k , βk=t) = ∣ n , Pn ∣₁
    where
    nm : ℕ × ℕ
    nm = cantorUnpair k
    n = fst nm
    m = snd nm
    αnm=t : αP n m ≡ true
    αnm=t = βk=t
    exists→Pn = snd (snd (αs n))
    Pn : ⟨ P n ⟩
    Pn = exists→Pn (m , αnm=t)

  forward : ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁ → Σ[ k ∈ ℕ ] β k ≡ true
  forward truncExists = mp β ¬allFalse
    where
    ¬allFalse : ¬ ((k : ℕ) → β k ≡ false)
    ¬allFalse allFalse = PT.rec isProp⊥ helper truncExists
      where
      helper : Σ[ n ∈ ℕ ] ⟨ P n ⟩ → ⊥
      helper (n , pn) =
        let Pn→exists = fst (snd (αs n))
            (m , αnm=t) = Pn→exists pn
            k = cantorPair n m
            βk=t : β k ≡ true
            βk=t =
              β k
                ≡⟨ refl ⟩
              αP (fst (cantorUnpair k)) (snd (cantorUnpair k))
                ≡⟨ cong (λ p → αP (fst p) (snd p)) (cantorUnpair-pair n m) ⟩
              αP n m
                ≡⟨ αnm=t ⟩
              true ∎
        in false≢true (sym (allFalse k) ∙ βk=t)

⋀-Closed : (ℕ → Closed) → Closed
⋀-Closed Cs = (((n : ℕ) → ⟨ fst (Cs n) ⟩) , isPropΠ (λ n → snd (fst (Cs n)))) ,
              closedCountableIntersection (λ n → fst (Cs n)) (λ n → snd (Cs n))

⋁-Open : (ℕ → Open) → Open
⋁-Open Os = ((∥ Σ[ n ∈ ℕ ] ⟨ fst (Os n) ⟩ ∥₁) , squash₁) ,
            openCountableUnion (λ n → fst (Os n)) (λ n → snd (Os n))

-- (ClopenDecidable from tex Corollary 774)

isProp⊎¬ : (P : hProp ℓ-zero) → isProp (⟨ P ⟩ ⊎ (¬ ⟨ P ⟩))
isProp⊎¬ P (inl p) (inl p') = cong inl (snd P p p')
isProp⊎¬ P (inl p) (inr ¬p) = ex-falso (¬p p)
isProp⊎¬ P (inr ¬p) (inl p) = ex-falso (¬p p)
isProp⊎¬ P (inr ¬p) (inr ¬p') = cong inr (isProp¬ ⟨ P ⟩ ¬p ¬p')

clopenIsDecidable : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp P → Dec ⟨ P ⟩
clopenIsDecidable P Popen Pclosed =
  let -- ¬P is open because P is closed (and we have MP)
      ¬P : hProp ℓ-zero
      ¬P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩

      ¬Popen : isOpenProp ¬P
      ¬Popen = negClosedIsOpen mp P Pclosed

      P∨¬P-trunc : hProp ℓ-zero
      P∨¬P-trunc = (∥ ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩) ∥₁) , squash₁

      P∨¬P-trunc-open : isOpenProp P∨¬P-trunc
      P∨¬P-trunc-open = openOr P ¬P Popen ¬Popen

      ¬¬P∨¬P-trunc : ¬ ¬ ∥ ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩) ∥₁
      ¬¬P∨¬P-trunc k = k ∣ inr (λ p → k ∣ inl p ∣₁) ∣₁

      P∨¬P-trunc-holds : ∥ ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩) ∥₁
      P∨¬P-trunc-holds = openIsStable mp P∨¬P-trunc P∨¬P-trunc-open ¬¬P∨¬P-trunc

      P∨¬P-holds : ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩)
      P∨¬P-holds = PT.rec (isProp⊎¬ P) (λ x → x) P∨¬P-trunc-holds

  in ⊎-rec (λ p → yes p) (λ ¬p → no ¬p) P∨¬P-holds
  where
  ⊎-rec : {A B C : Type} → (A → C) → (B → C) → A ⊎ B → C
  ⊎-rec f g (inl a) = f a
  ⊎-rec f g (inr b) = g b

-- (ImplicationOpenClosed from tex Lemma 857)

implicationOpenClosed : (P Q : hProp ℓ-zero) → isOpenProp P → isClosedProp Q
                      → isClosedProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
implicationOpenClosed P Q Popen Qclosed = γ , forward , backward
  where
  ¬Q : hProp ℓ-zero
  ¬Q = (¬ ⟨ Q ⟩) , isProp¬ ⟨ Q ⟩

  ¬Qopen : isOpenProp ¬Q
  ¬Qopen = negClosedIsOpen mp Q Qclosed

  P∧¬Q : hProp ℓ-zero
  P∧¬Q = (⟨ P ⟩ × (¬ ⟨ Q ⟩)) , isProp× (snd P) (isProp¬ ⟨ Q ⟩)

  P∧¬Qopen : isOpenProp P∧¬Q
  P∧¬Qopen = openAnd P ¬Q Popen ¬Qopen

  ¬P∧¬Qclosed : isClosedProp (¬hProp P∧¬Q)
  ¬P∧¬Qclosed = negOpenIsClosed P∧¬Q P∧¬Qopen

  γ : binarySequence
  γ = fst ¬P∧¬Qclosed

  forward : (⟨ P ⟩ → ⟨ Q ⟩) → (n : ℕ) → γ n ≡ false
  forward p→q = fst (snd ¬P∧¬Qclosed) ¬P∧¬Q-holds
    where
    ¬P∧¬Q-holds : ¬ (⟨ P ⟩ × (¬ ⟨ Q ⟩))
    ¬P∧¬Q-holds (p , ¬q) = ¬q (p→q p)

  backward : ((n : ℕ) → γ n ≡ false) → ⟨ P ⟩ → ⟨ Q ⟩
  backward all-false p =
    let ¬P∧¬Q-holds : ¬ (⟨ P ⟩ × (¬ ⟨ Q ⟩))
        ¬P∧¬Q-holds = snd (snd ¬P∧¬Qclosed) all-false
        ¬¬Q : ¬ ¬ ⟨ Q ⟩
        ¬¬Q ¬q = ¬P∧¬Q-holds (p , ¬q)
    in closedIsStable (⟨ Q ⟩ , snd Q) Qclosed ¬¬Q

closedMarkovTex : (P : ℕ → hProp ℓ-zero) → ((n : ℕ) → isClosedProp (P n))
                → (¬ ((n : ℕ) → ⟨ P n ⟩)) ↔ ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
closedMarkovTex P Pclosed = forward , backward
  where
  ∀P-closed : isClosedProp (((n : ℕ) → ⟨ P n ⟩) , isPropΠ (λ n → snd (P n)))
  ∀P-closed = closedCountableIntersection P Pclosed

  ¬∀P-open : isOpenProp ((¬ ((n : ℕ) → ⟨ P n ⟩)) , isProp¬ _)
  ¬∀P-open = negClosedIsOpen mp (((n : ℕ) → ⟨ P n ⟩) , isPropΠ (λ n → snd (P n))) ∀P-closed

  ¬Pn-open : (n : ℕ) → isOpenProp ((¬ ⟨ P n ⟩) , isProp¬ _)
  ¬Pn-open n = negClosedIsOpen mp (P n) (Pclosed n)

  ∃¬P-open : isOpenProp (∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ , squash₁)
  ∃¬P-open = openCountableUnion (λ n → (¬ ⟨ P n ⟩) , isProp¬ _) ¬Pn-open

  forward : ¬ ((n : ℕ) → ⟨ P n ⟩) → ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
  forward ¬∀P =
    let ¬¬∃¬P : ¬ ¬ ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
        ¬¬∃¬P k = ¬∀P (λ n →
          closedIsStable (P n) (Pclosed n)
            (λ ¬Pn → k ∣ n , ¬Pn ∣₁))
    in openIsStable mp (∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ , squash₁) ∃¬P-open ¬¬∃¬P

  backward : ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ → ¬ ((n : ℕ) → ⟨ P n ⟩)
  backward = PT.rec (isProp¬ _) (λ { (n , ¬Pn) ∀P → ¬Pn (∀P n) })

openSigmaDecidable : (D : hProp ℓ-zero) → Dec ⟨ D ⟩
                   → (Q : ⟨ D ⟩ → hProp ℓ-zero) → ((d : ⟨ D ⟩) → isOpenProp (Q d))
                   → isOpenProp (∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ , squash₁)
openSigmaDecidable D (yes d) Q Qopen = α , forward , backward
  where
  α = Qopen d .fst
  Qd→∃ = fst (snd (Qopen d))
  ∃→Qd = snd (snd (Qopen d))

  forward : ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁ → Σ[ n ∈ ℕ ] α n ≡ true
  forward truncExists = mp α ¬allFalse
    where
    ¬allFalse : ¬ ((n : ℕ) → α n ≡ false)
    ¬allFalse allFalse = PT.rec isProp⊥ helper truncExists
      where
      helper : Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ → ⊥
      helper (d' , q) =
        let q' = subst (λ x → ⟨ Q x ⟩) (snd D d' d) q
            (n , αn=t) = Qd→∃ q'
        in false≢true (sym (allFalse n) ∙ αn=t)

  backward : Σ[ n ∈ ℕ ] α n ≡ true → ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁
  backward w = ∣ d , ∃→Qd w ∣₁

openSigmaDecidable D (no ¬d) Q Qopen = α , forward , backward
  where
  α = ⊥-isOpen .fst

  forward : ∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ → Σ[ n ∈ ℕ ] α n ≡ true
  forward x = ex-falso (PT.rec isProp⊥ (λ { (d , _) → ¬d d }) x)

  backward : Σ[ n ∈ ℕ ] α n ≡ true → ∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁
  backward (n , αn=t) = ex-falso (true≢false (sym αn=t))

-- Open propositions are closed under Σ-types (tex Corollary OpenDependentSums 1313)

openSigmaOpen : (P : hProp ℓ-zero) → isOpenProp P
              → (Q : ⟨ P ⟩ → hProp ℓ-zero) → ((p : ⟨ P ⟩) → isOpenProp (Q p))
              → isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
openSigmaOpen P (α , P→∃ , ∃→P) Q Qopen = result
  where
  Dn : ℕ → hProp ℓ-zero
  Dn n = (α n ≡ true) , isSetBool _ _

  Dn-dec : (n : ℕ) → Dec (α n ≡ true)
  Dn-dec n = α n =B true

  witness : (n : ℕ) → (α n ≡ true) → ⟨ P ⟩
  witness n = λ eq → ∃→P (n , eq)

  Rn : ℕ → hProp ℓ-zero
  Rn n = (∥ Σ[ eq ∈ (α n ≡ true) ] ⟨ Q (witness n eq) ⟩ ∥₁) , squash₁

  Rn-open : (n : ℕ) → isOpenProp (Rn n)
  Rn-open n = openSigmaDecidable (Dn n) (Dn-dec n)
                (λ eq → Q (witness n eq))
                (λ eq → Qopen (witness n eq))

  countableUnionOpen : isOpenProp (∥ Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ ∥₁ , squash₁)
  countableUnionOpen = openCountableUnion Rn Rn-open

  forward-equiv : ∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ → ∥ Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ ∥₁
  forward-equiv = PT.rec squash₁ helper
    where
    helper : Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ → ∥ Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ ∥₁
    helper (p , qp) = ∣ n , ∣ αn=t , qp' ∣₁ ∣₁
      where
      n = fst (P→∃ p)
      αn=t = snd (P→∃ p)
      p' = witness n αn=t
      p≡p' = snd P p p'
      qp' : ⟨ Q (witness n αn=t) ⟩
      qp' = subst (λ x → ⟨ Q x ⟩) p≡p' qp

  backward-equiv : ∥ Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ ∥₁ → ∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁
  backward-equiv = PT.rec squash₁ helper1
    where
    helper1 : Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ → ∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁
    helper1 (n , rn) = PT.rec squash₁ helper2 rn
      where
      helper2 : Σ[ eq ∈ (α n ≡ true) ] ⟨ Q (witness n eq) ⟩ → ∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁
      helper2 (αn=t , qw) = ∣ witness n αn=t , qw ∣₁

  result : isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
  result =
    let (β , union→∃ , ∃→union) = countableUnionOpen
    in β ,
       (λ sigPQ → union→∃ (forward-equiv sigPQ)) ,
       (λ w → backward-equiv (∃→union w))

open→¬¬stable : (P : hProp ℓ-zero) → isOpenProp P → (¬ ¬ ⟨ P ⟩ → ⟨ P ⟩)
open→¬¬stable P Popen = openIsStable mp P Popen

closed→¬¬stable : (P : hProp ℓ-zero) → isClosedProp P → (¬ ¬ ⟨ P ⟩ → ⟨ P ⟩)
closed→¬¬stable P Pclosed = closedIsStable P Pclosed

closed→¬open : (P : hProp ℓ-zero) → isClosedProp P → isOpenProp (¬hProp P)
closed→¬open P = negClosedIsOpen mp P

¬open→closed : (P : hProp ℓ-zero) → isOpenProp (¬hProp P) → isClosedProp (¬¬hProp P)
¬open→closed P ¬Popen = negOpenIsClosed (¬hProp P) ¬Popen

openEquiv : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩)
          → isOpenProp P → isOpenProp Q
openEquiv P Q P→Q Q→P (α , P→∃ , ∃→P) =
  α , (λ q → P→∃ (Q→P q)) , (λ w → P→Q (∃→P w))

closedEquiv : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩)
            → isClosedProp P → isClosedProp Q
closedEquiv P Q P→Q Q→P (α , P→∀ , ∀→P) =
  α , (λ q → P→∀ (Q→P q)) , (λ w → P→Q (∀→P w))

-- Decidable ↔ both open and closed (tex Corollary ClopenDecidable + remark)

decidable→open×closed : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isOpenProp P × isClosedProp P
decidable→open×closed P dec = decIsOpen P dec , decIsClosed P dec

open×closed→decidable : (P : hProp ℓ-zero) → isOpenProp P × isClosedProp P → Dec ⟨ P ⟩
open×closed→decidable P (Popen , Pclosed) = clopenIsDecidable P Popen Pclosed

decidable↔open×closed : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ ↔ (isOpenProp P × isClosedProp P)
decidable↔open×closed P = decidable→open×closed P , open×closed→decidable P

-- Definition (tex line 884-886):

isOpenSubset : {T : Type₀} → (A : T → hProp ℓ-zero) → Type₀
isOpenSubset {T} A = (t : T) → isOpenProp (A t)

isClosedSubset : {T : Type₀} → (A : T → hProp ℓ-zero) → Type₀
isClosedSubset {T} A = (t : T) → isClosedProp (A t)

-- The pre-image of an open subset under any map is open (tex remark 889)
preimageOpenIsOpen : {S T : Type₀} (f : S → T) (A : T → hProp ℓ-zero)
                   → isOpenSubset A → isOpenSubset (λ s → A (f s))
preimageOpenIsOpen f A Aopen s = Aopen (f s)

-- Transitivity of openness (tex Corollary OpenTransitive 1319)
openSubsetTransitive : {T : Type₀}
                     → (V : T → hProp ℓ-zero) → isOpenSubset V
                     → (W : (t : T) → ⟨ V t ⟩ → hProp ℓ-zero)
                     → ((t : T) (v : ⟨ V t ⟩) → isOpenProp (W t v))
                     → isOpenSubset (λ t → (∥ Σ[ v ∈ ⟨ V t ⟩ ] ⟨ W t v ⟩ ∥₁) , squash₁)
openSubsetTransitive V Vopen W Wopen t =
  openSigmaOpen (V t) (Vopen t) (W t) (Wopen t)

-- Remark: Open forms a dominance (tex Remark OpenDominance 1330)

-- Remark: Closed forms a dominance (tex Remark ClosedDominance 1794)

-- Surjection from 2^ℕ to Closed (tex line 1753)

allFalseProp : binarySequence → hProp ℓ-zero
allFalseProp α = ((n : ℕ) → α n ≡ false) , isPropΠ (λ n → isSetBool (α n) false)

binarySeqToClosed : binarySequence → Closed
binarySeqToClosed α = allFalseProp α , allFalseIsClosed α

