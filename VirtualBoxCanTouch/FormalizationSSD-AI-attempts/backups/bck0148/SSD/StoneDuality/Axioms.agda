{-# OPTIONS --cubical --guardedness #-}

-- tex Section 1.2: Axioms (lines 282-371)

module SSD.StoneDuality.Axioms where

open import SSD.StoneDuality.Preliminaries public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties using (isProp⊎)

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import SSD.Library.StoneDuality using (StoneDualityAxiom; Sp; Booleω)

import SSD.Library.Markov as MarkovLib

open import SSD.Library.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; invBooleanRingEquiv; idBoolHom)
open import SSD.Library.Examples.Bool using (is-cp-2)
open import SSD.Library.FreeBooleanRing.FreeBool using (freeBA)
import SSD.Library.QuotientBool as QB
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
import Cubical.Data.Sum as ⊎

-- tex Axiom 285: Stone Duality (AxStoneDuality)
-- (StoneDualityAxiom is defined in SSD.Library.StoneDuality)

-- tex Axiom 294-297: Surjections are formal surjections (SurjectionsAreFormalSurjections)

isInjectiveBoolHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isInjectiveBoolHom B C g = (x y : ⟨ fst B ⟩) → fst g x ≡ fst g y → x ≡ y

isSurjectiveSpHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isSurjectiveSpHom B C g = (h : Sp B) → ∥ Σ[ h' ∈ Sp C ] h' ∘cr g ≡ h ∥₁

SurjectionsAreFormalSurjectionsAxiom : Type (ℓ-suc ℓ-zero)
SurjectionsAreFormalSurjectionsAxiom = (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isInjectiveBoolHom B C g ↔ isSurjectiveSpHom B C g

-- tex Axiom 348-353: Local choice (AxLocalChoice)

isSurjectiveSpMap : {B C : Booleω} → (Sp C → Sp B) → Type ℓ-zero
isSurjectiveSpMap {B} {C} q = (h : Sp B) → ∥ Σ[ h' ∈ Sp C ] q h' ≡ h ∥₁

LocalChoiceAxiom : Type (ℓ-suc ℓ-zero)
LocalChoiceAxiom = (B : Booleω) (P : Sp B → Type ℓ-zero)
  → ((s : Sp B) → ∥ P s ∥₁)
  → ∥ Σ[ C ∈ Booleω ] Σ[ q ∈ (Sp C → Sp B) ]
      (isSurjectiveSpMap {B} {C} q × ((t : Sp C) → P (q t))) ∥₁

-- tex Axiom 324: Dependent choice (AxDependentChoice)

SeqLimit : (E : ℕ → Type ℓ-zero) → ((n : ℕ) → E (suc n) → E n) → Type ℓ-zero
SeqLimit E p = Σ[ f ∈ ((n : ℕ) → E n) ] ((n : ℕ) → p n (f (suc n)) ≡ f n)

seqLim-proj₀ : (E : ℕ → Type ℓ-zero) (p : (n : ℕ) → E (suc n) → E n)
             → SeqLimit E p → E 0
seqLim-proj₀ E p (f , _) = f 0

DependentChoiceAxiom : Type (ℓ-suc ℓ-zero)
DependentChoiceAxiom = (E : ℕ → Type ℓ-zero) (p : (n : ℕ) → E (suc n) → E n)
  → ((n : ℕ) → (y : E n) → ∥ Σ[ x ∈ E (suc n) ] p n x ≡ y ∥₁)
  → (e₀ : E 0) → ∥ Σ[ s ∈ SeqLimit E p ] seqLim-proj₀ E p s ≡ e₀ ∥₁

CountableChoiceAxiom : Type (ℓ-suc ℓ-zero)
CountableChoiceAxiom = (A : ℕ → Type ℓ-zero)
  → ((n : ℕ) → ∥ A n ∥₁)
  → ∥ ((n : ℕ) → A n) ∥₁

-- Record of all axioms (replaces postulates)

record Axioms : Type (ℓ-suc ℓ-zero) where
  field
    sd : StoneDualityAxiom
    surj-formal : SurjectionsAreFormalSurjectionsAxiom
    localChoice : LocalChoiceAxiom
    depChoice : DependentChoiceAxiom
    llpo-ax : LLPO

-- Module parameterized over axioms (all subsequent modules use this pattern)

module WithAxioms (axioms : Axioms) where
  open Axioms axioms public

  -- Derived principles

  -- tex Lemma 406: Spectrum empty iff 0=1
  module SpectrumEmptyImpliesTrivial (B : Booleω) (spEmpty : Sp B → ⊥) where
    open import SSD.Library.StoneDuality using (evaluationMap)

    emptyFunContr : isContr (Sp B → Bool)
    emptyFunContr = (λ sp → ex-falso (spEmpty sp)) , λ f → funExt (λ sp → ex-falso (spEmpty sp))

    B-contr : isContr ⟨ fst B ⟩
    B-contr = isOfHLevelRespectEquiv 0 (invEquiv (evaluationMap B , sd B)) emptyFunContr

    0≡1-in-B : BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B))
    0≡1-in-B = isContr→isProp B-contr _ _

  -- BoolQuotientEquiv (needed for quotient constructions)
  postulate
    BoolQuotientEquiv : (A : BooleanRing ℓ-zero) (f g : ℕ → ⟨ A ⟩) →
      BooleanRing→CommRing (A QB./Im (⊎.rec f g)) ≡
      BooleanRing→CommRing ((A QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))

  open import Cubical.Algebra.CommRing.Properties using (compCommRingEquiv)

  compBoolRingEquiv : (A B C : BooleanRing ℓ-zero)
                    → BooleanRingEquiv A B → BooleanRingEquiv B C → BooleanRingEquiv A C
  compBoolRingEquiv A B C f g = compCommRingEquiv {A = BooleanRing→CommRing A} {B = BooleanRing→CommRing B} {C = BooleanRing→CommRing C} f g

  open import Cubical.Algebra.CommRing.Univalence using (CommRingPath)

  commRingPath→boolRingEquiv : (A B : BooleanRing ℓ-zero)
    → BooleanRing→CommRing A ≡ BooleanRing→CommRing B
    → BooleanRingEquiv A B
  commRingPath→boolRingEquiv A B p =
    let e = invEq (CommRingPath _ _) p in fst e , snd e

  Bool-Booleω : Booleω
  Bool-Booleω = BoolBR , ∣ is-cp-2 ∣₁

  Sp-Bool-inhabited : ∥ Sp Bool-Booleω ∥₁
  Sp-Bool-inhabited = ∣ idBoolHom BoolBR ∣₁

  quotientPreservesBooleω : (α : binarySequence) → ∥ has-Boole-ω' (BoolBR QB./Im α) ∥₁
  quotientPreservesBooleω α = ∣ presentationWitness ∣₁
    where
    f₀ : ℕ → ⟨ freeBA ℕ ⟩
    f₀ = fst is-cp-2

    equiv : BooleanRingEquiv BoolBR (freeBA ℕ QB./Im f₀)
    equiv = snd is-cp-2

    π₀ : ⟨ freeBA ℕ ⟩ → ⟨ freeBA ℕ QB./Im f₀ ⟩
    π₀ = fst QB.quotientImageHom

    embBR : ⟨ BoolBR ⟩ → ⟨ freeBA ℕ QB./Im f₀ ⟩
    embBR = fst (fst equiv)

    α' : ℕ → ⟨ freeBA ℕ QB./Im f₀ ⟩
    α' n = embBR (α n)

    encode : ℕ ⊎ ℕ → ℕ
    encode = Iso.fun ℕ⊎ℕ≅ℕ

    decode : ℕ → ℕ ⊎ ℕ
    decode = Iso.inv ℕ⊎ℕ≅ℕ

    open BooleanRingStr (snd (freeBA ℕ))

    g : ℕ → ⟨ freeBA ℕ ⟩
    g n = if (α n) then 𝟙 else 𝟘

    h : ℕ → ⟨ freeBA ℕ ⟩
    h n with decode n
    ... | inl m = f₀ m
    ... | inr m = g m

    presentationWitness : has-Boole-ω' (BoolBR QB./Im α)
    presentationWitness = h , equivToPresentation
      where

      step2-equiv : BooleanRingEquiv (freeBA ℕ QB./Im (⊎.rec f₀ g)) ((freeBA ℕ QB./Im f₀) QB./Im (π₀ ∘ g))
      step2-equiv = commRingPath→boolRingEquiv (freeBA ℕ QB./Im (⊎.rec f₀ g)) ((freeBA ℕ QB./Im f₀) QB./Im (π₀ ∘ g))
                      (BoolQuotientEquiv (freeBA ℕ) f₀ g)

      h≡rec∘decode-pointwise : (n : ℕ) → h n ≡ ⊎.rec f₀ g (decode n)
      h≡rec∘decode-pointwise n with decode n
      ... | inl m = refl
      ... | inr m = refl

      rec-of-decode : (n : ℕ) → ⊎.rec f₀ g (decode n) ≡ h n
      rec-of-decode n = sym (h≡rec∘decode-pointwise n)

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
          ≡⟨ cong (⊎.rec f₀ g) (sym (Iso.ret ℕ⊎ℕ≅ℕ x)) ⟩
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
      step3-forward-eval = QB.evalInduce {B = freeBA ℕ} {f = h} rec-quotient

      step3-backward-eval : step3-backward-hom ∘cr π-rec ≡ π-h
      step3-backward-eval = QB.evalInduce {B = freeBA ℕ} {f = ⊎.rec f₀ g} h-quotient

      step3-backward∘forward-on-π : (x : ⟨ freeBA ℕ ⟩) → step3-backward (step3-forward (fst π-h x)) ≡ fst π-h x
      step3-backward∘forward-on-π x =
        step3-backward (step3-forward (fst π-h x))
          ≡⟨ cong step3-backward (cong (λ f → fst f x) step3-forward-eval) ⟩
        step3-backward (fst π-rec x)
          ≡⟨ cong (λ f → fst f x) step3-backward-eval ⟩
        fst π-h x ∎

      step3-forward∘backward-on-π : (y : ⟨ freeBA ℕ ⟩) → step3-forward (step3-backward (fst π-rec y)) ≡ fst π-rec y
      step3-forward∘backward-on-π y =
        step3-forward (step3-backward (fst π-rec y))
          ≡⟨ cong step3-forward (cong (λ f → fst f y) step3-backward-eval) ⟩
        step3-forward (fst π-h y)
          ≡⟨ cong (λ f → fst f y) step3-forward-eval ⟩
        fst π-rec y ∎

      step3-iso : Iso ⟨ h-quotient ⟩ ⟨ rec-quotient ⟩
      Iso.fun step3-iso = step3-forward
      Iso.inv step3-iso = step3-backward
      Iso.sec step3-iso = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = ⊎.rec f₀ g}
        (⟨ rec-quotient ⟩ , BooleanRingStr.is-set (snd rec-quotient)) (funExt step3-forward∘backward-on-π))
      Iso.ret step3-iso = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = h}
        (⟨ h-quotient ⟩ , BooleanRingStr.is-set (snd h-quotient)) (funExt step3-backward∘forward-on-π))

      step3-equiv : BooleanRingEquiv (freeBA ℕ QB./Im h) (freeBA ℕ QB./Im (⊎.rec f₀ g))
      step3-equiv = isoToEquiv step3-iso , snd step3-forward-hom

      target : BooleanRing ℓ-zero
      target = (freeBA ℕ QB./Im f₀) QB./Im α'

      π-α' : BoolHom (freeBA ℕ QB./Im f₀) target
      π-α' = QB.quotientImageHom

      composite-hom : BoolHom BoolBR target
      composite-hom = π-α' ∘cr (fst (fst equiv) , snd equiv)

      forward-hom : BoolHom (BoolBR QB./Im α) target
      forward-hom = QB.inducedHom target composite-hom (λ n → QB.zeroOnImage {f = α'} n)

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
        π-α $cr (equiv⁻¹-hom $cr (embBR (α n)))
          ≡⟨ cong (π-α $cr_) (Iso.ret (equivToIso (fst equiv)) (α n)) ⟩
        π-α $cr (α n)
          ≡⟨ QB.zeroOnImage {f = α} n ⟩
        BooleanRingStr.𝟘 (snd source) ∎

      backward-hom : BoolHom target source
      backward-hom = QB.inducedHom source backward-composite backward-composite-sends-α'-to-0

      forward-eval : forward-hom ∘cr π-α ≡ composite-hom
      forward-eval = QB.evalInduce {B = BoolBR} {f = α} target

      backward-eval : backward-hom ∘cr π-α' ≡ backward-composite
      backward-eval = QB.evalInduce {B = freeBA ℕ QB./Im f₀} {f = α'} source

      backward∘forward-on-π : (x : Bool) → fst backward-hom (fst forward-hom (fst π-α x)) ≡ fst π-α x
      backward∘forward-on-π x =
        fst backward-hom (fst forward-hom (fst π-α x))
          ≡⟨ cong (fst backward-hom) (cong (λ h → fst h x) forward-eval) ⟩
        fst backward-hom (fst composite-hom x)
          ≡⟨ cong (λ h → fst h (embBR x)) backward-eval ⟩
        fst π-α (fst equiv⁻¹-hom (embBR x))
          ≡⟨ cong (fst π-α) (Iso.ret (equivToIso (fst equiv)) x) ⟩
        fst π-α x ∎

      forward∘backward-on-π : (y : ⟨ freeBA ℕ QB./Im f₀ ⟩) → fst forward-hom (fst backward-hom (fst π-α' y)) ≡ fst π-α' y
      forward∘backward-on-π y =
        fst forward-hom (fst backward-hom (fst π-α' y))
          ≡⟨ cong (fst forward-hom) (cong (λ h → fst h y) backward-eval) ⟩
        fst forward-hom (fst backward-composite y)
          ≡⟨ cong (λ h → fst h (fst equiv⁻¹-hom y)) forward-eval ⟩
        fst π-α' (embBR (fst equiv⁻¹-hom y))
          ≡⟨ cong (fst π-α') (Iso.sec (equivToIso (fst equiv)) y) ⟩
        fst π-α' y ∎

      step1-iso : Iso ⟨ source ⟩ ⟨ target ⟩
      Iso.fun step1-iso = fst forward-hom
      Iso.inv step1-iso = fst backward-hom
      Iso.sec step1-iso = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ QB./Im f₀} {f = α'}
        (⟨ target ⟩ , BooleanRingStr.is-set (snd target)) (funExt forward∘backward-on-π))
      Iso.ret step1-iso = funExt⁻ (QB.quotientImageHomEpi {B = BoolBR} {f = α}
        (⟨ source ⟩ , BooleanRingStr.is-set (snd source)) (funExt backward∘forward-on-π))

      open IsCommRingHom

      α'≡π₀∘g-pointwise : (n : ℕ) → α' n ≡ π₀ (g n)
      α'≡π₀∘g-pointwise n with α n
      ... | true  = pres1 (snd equiv) ∙ sym (pres1 (snd QB.quotientImageHom))
      ... | false = pres0 (snd equiv) ∙ sym (pres0 (snd QB.quotientImageHom))

      A' = BoolBR QB./Im α
      B' = (freeBA ℕ QB./Im f₀) QB./Im (π₀ ∘ g)

      equivToPresentation : BooleanRingEquiv (BoolBR QB./Im α) (freeBA ℕ QB./Im h)
      equivToPresentation = compBoolRingEquiv A' rec-quotient h-quotient
        (compBoolRingEquiv A' B' rec-quotient
          (subst (λ f → BooleanRingEquiv A' ((freeBA ℕ QB./Im f₀) QB./Im f))
                 (funExt α'≡π₀∘g-pointwise)
                 (isoToEquiv step1-iso , snd forward-hom))
          (invBooleanRingEquiv rec-quotient B' step2-equiv))
        (invBooleanRingEquiv h-quotient rec-quotient step3-equiv)

  2/α-Booleω : (α : binarySequence) → Booleω
  2/α-Booleω α = (BoolBR QB./Im α) , quotientPreservesBooleω α

  -- tex Corollary 530: Markov Principle from Stone Duality
  mp-from-SD : MarkovPrinciple
  mp-from-SD α α≠0 = MarkovLib.extract' α (MarkovLib.∃αn α (trivialQuotient→1∈I BoolCR (IQ.genIdeal BoolCR α) (sym 0≡1-CR)))
    where
    open import SSD.Library.StoneDuality using (evaluationMap)
    open import SSD.Library.CommRingQuotients.TrivialIdeal using (trivialQuotient→1∈I)
    import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ

    BoolCR = BooleanRing→CommRing BoolBR

    0≡1-BR : BooleanRingStr.𝟘 (snd (BoolBR QB./Im α)) ≡ BooleanRingStr.𝟙 (snd (BoolBR QB./Im α))
    0≡1-BR = SpectrumEmptyImpliesTrivial.0≡1-in-B (2/α-Booleω α) (MarkovLib.emptySp α α≠0)

    open import SSD.Library.QuotientBool using (_/Im_)
    opaque
      unfolding _/Im_
      0≡1-CR : CommRingStr.0r (snd (BoolCR IQ./Im α)) ≡ CommRingStr.1r (snd (BoolCR IQ./Im α))
      0≡1-CR = 0≡1-BR

  mp : MarkovPrinciple
  mp = mp-from-SD

  -- tex Corollary 415: injective→Sp-surjective
  injective→Sp-surjective : (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
    isInjectiveBoolHom B C g → isSurjectiveSpHom B C g
  injective→Sp-surjective B C g = fst (surj-formal B C g)

  -- Countable choice from dependent choice
  countableChoice : CountableChoiceAxiom
  countableChoice A witnesses = PT.map (λ { ((f , _) , _) n → snd (f (suc n)) })
      (depChoice E p p-surj tt)
    where
    E : ℕ → Type ℓ-zero
    E zero = Unit
    E (suc n) = E n × A n

    p : (n : ℕ) → E (suc n) → E n
    p n (e , _) = e

    p-surj : (n : ℕ) → (y : E n) → ∥ Σ[ x ∈ E (suc n) ] p n x ≡ y ∥₁
    p-surj n y = PT.map (λ a → (y , a) , refl) (witnesses n)

  -- ∞ : ℕ∞
  ∞ : ℕ∞
  ∞ = (λ _ → false) , (λ m n αm=t _ → ex-falso (false≢true αm=t))

  -- tex Theorem 500: Markov principle for ℕ∞
  ℕ∞-Markov : (α : ℕ∞) → ¬ ((n : ℕ) → fst α n ≡ false) → Σ[ n ∈ ℕ ] fst α n ≡ true
  ℕ∞-Markov α = mp (fst α)
