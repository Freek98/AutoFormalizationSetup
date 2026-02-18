{-# OPTIONS --cubical --guardedness #-}

module work.Part02 where

open import work.Part01 public

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
open import Axioms.StoneDuality using (StoneDualityAxiom; Sp; Booleω)

import OmnisciencePrinciples.Markov as MarkovLib

open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; invBooleanRingEquiv; idBoolHom)
open import CountablyPresentedBooleanRings.Examples.Bool using (is-cp-2)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA)
import QuotientBool as QB
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
import Cubical.Data.Sum as ⊎

module SpectrumEmptyImpliesTrivial (SD : StoneDualityAxiom) (B : Booleω) (spEmpty : Sp B → ⊥) where
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
commRingPath→boolRingEquiv A B p =
  let e = invEq (CommRingPath _ _) p in fst e , snd e

Bool-Booleω : Booleω
Bool-Booleω = BoolBR , ∣ is-cp-2 ∣₁

Sp-Bool-inhabited : ∥ Sp Bool-Booleω ∥₁
Sp-Bool-inhabited = ∣ idBoolHom BoolBR ∣₁

-- Dependent Choice axiom (tex line 324, AxDependentChoice)

SeqLimit : (E : ℕ → Type ℓ-zero) → ((n : ℕ) → E (suc n) → E n) → Type ℓ-zero
SeqLimit E p = Σ[ f ∈ ((n : ℕ) → E n) ] ((n : ℕ) → p n (f (suc n)) ≡ f n)

seqLim-proj₀ : (E : ℕ → Type ℓ-zero) (p : (n : ℕ) → E (suc n) → E n)
             → SeqLimit E p → E 0
seqLim-proj₀ E p (f , _) = f 0

DependentChoiceAxiom : Type (ℓ-suc ℓ-zero)
DependentChoiceAxiom = (E : ℕ → Type ℓ-zero) (p : (n : ℕ) → E (suc n) → E n)
  → ((n : ℕ) → (y : E n) → ∥ Σ[ x ∈ E (suc n) ] p n x ≡ y ∥₁)
  → (e₀ : E 0) → ∥ Σ[ s ∈ SeqLimit E p ] seqLim-proj₀ E p s ≡ e₀ ∥₁

postulate
  dependentChoice-axiom : DependentChoiceAxiom

CountableChoiceAxiom : Type (ℓ-suc ℓ-zero)
CountableChoiceAxiom = (A : ℕ → Type ℓ-zero)
  → ((n : ℕ) → ∥ A n ∥₁)
  → ∥ ((n : ℕ) → A n) ∥₁

countableChoice : CountableChoiceAxiom
countableChoice A witnesses = PT.map (λ { ((f , _) , _) n → snd (f (suc n)) })
    (dependentChoice-axiom E p p-surj tt)
  where
  E : ℕ → Type ℓ-zero
  E zero = Unit
  E (suc n) = E n × A n

  p : (n : ℕ) → E (suc n) → E n
  p n (e , _) = e

  p-surj : (n : ℕ) → (y : E n) → ∥ Σ[ x ∈ E (suc n) ] p n x ≡ y ∥₁
  p-surj n y = PT.map (λ a → (y , a) , refl) (witnesses n)

-- If B is Booleω, then B/d is Booleω for any sequence d (tex: Rule 2 separation)

quotientBySeqHasBooleω : (B : Booleω) (d : ℕ → ⟨ fst B ⟩)
  → ∥ has-Boole-ω' (fst B QB./Im d) ∥₁
quotientBySeqHasBooleω B d = PT.rec squash₁ construct (snd B)
  where
  B/d : BooleanRing ℓ-zero
  B/d = fst B QB./Im d

  construct : has-Boole-ω' (fst B) → ∥ has-Boole-ω' B/d ∥₁
  construct (f , equiv) = PT.rec squash₁ (λ lifts → ∣ constructFromLifts lifts ∣₁)
      (countableChoice LiftType (λ n → QB.quotientImageHomSurjective (d' n)))
    where
    d' : ℕ → ⟨ freeBA ℕ QB./Im f ⟩
    d' n = fst (fst equiv) (d n)

    LiftType : ℕ → Type ℓ-zero
    LiftType n = Σ[ x ∈ ⟨ freeBA ℕ ⟩ ] fst QB.quotientImageHom x ≡ d' n

    constructFromLifts : ((n : ℕ) → LiftType n) → has-Boole-ω' B/d
    constructFromLifts lifts = h , B/d-equiv
      where
      g : ℕ → ⟨ freeBA ℕ ⟩
      g n = fst (lifts n)

      g-is-section : (n : ℕ) → fst QB.quotientImageHom (g n) ≡ d' n
      g-is-section n = snd (lifts n)

      encode : ℕ ⊎ ℕ → ℕ
      encode = Iso.fun ℕ⊎ℕ≅ℕ

      decode : ℕ → ℕ ⊎ ℕ
      decode = Iso.inv ℕ⊎ℕ≅ℕ

      h : ℕ → ⟨ freeBA ℕ ⟩
      h n with decode n
      ... | inl m = f m
      ... | inr m = g m

      step2-equiv : BooleanRingEquiv (freeBA ℕ QB./Im (⊎.rec f g))
                                     ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
      step2-equiv = commRingPath→boolRingEquiv
                      (freeBA ℕ QB./Im (⊎.rec f g))
                      ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
                      (BoolQuotientEquiv (freeBA ℕ) f g)

      h≡rec∘decode-pointwise : (n : ℕ) → h n ≡ ⊎.rec f g (decode n)
      h≡rec∘decode-pointwise n with decode n
      ... | inl m = refl
      ... | inr m = refl

      rec-quotient : BooleanRing ℓ-zero
      rec-quotient = freeBA ℕ QB./Im (⊎.rec f g)

      h-quotient : BooleanRing ℓ-zero
      h-quotient = freeBA ℕ QB./Im h

      π-rec : BoolHom (freeBA ℕ) rec-quotient
      π-rec = QB.quotientImageHom

      π-h : BoolHom (freeBA ℕ) h-quotient
      π-h = QB.quotientImageHom

      π-rec-sends-h-to-0 : (n : ℕ) → π-rec $cr (h n) ≡ BooleanRingStr.𝟘 (snd rec-quotient)
      π-rec-sends-h-to-0 n =
        π-rec $cr (h n)
          ≡⟨ cong (π-rec $cr_) (h≡rec∘decode-pointwise n) ⟩
        π-rec $cr ((⊎.rec f g) (decode n))
          ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = ⊎.rec f g} (decode n) ⟩
        BooleanRingStr.𝟘 (snd rec-quotient) ∎

      step3-forward-hom : BoolHom h-quotient rec-quotient
      step3-forward-hom = QB.inducedHom {B = freeBA ℕ} {f = h} rec-quotient π-rec π-rec-sends-h-to-0

      rec-eq-h-encode : (x : ℕ ⊎ ℕ) → (⊎.rec f g) x ≡ h (encode x)
      rec-eq-h-encode x =
        (⊎.rec f g) x
          ≡⟨ cong (⊎.rec f g) (sym (Iso.ret ℕ⊎ℕ≅ℕ x)) ⟩
        (⊎.rec f g) (decode (encode x))
          ≡⟨ sym (h≡rec∘decode-pointwise (encode x)) ⟩
        h (encode x) ∎

      π-h-sends-rec-to-0 : (x : ℕ ⊎ ℕ) → π-h $cr ((⊎.rec f g) x) ≡ BooleanRingStr.𝟘 (snd h-quotient)
      π-h-sends-rec-to-0 x =
        π-h $cr ((⊎.rec f g) x)
          ≡⟨ cong (π-h $cr_) (rec-eq-h-encode x) ⟩
        π-h $cr (h (encode x))
          ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = h} (encode x) ⟩
        BooleanRingStr.𝟘 (snd h-quotient) ∎

      step3-backward-hom : BoolHom rec-quotient h-quotient
      step3-backward-hom = QB.inducedHom {B = freeBA ℕ} {f = ⊎.rec f g} h-quotient π-h π-h-sends-rec-to-0

      step3-forward : ⟨ h-quotient ⟩ → ⟨ rec-quotient ⟩
      step3-forward = fst step3-forward-hom

      step3-backward : ⟨ rec-quotient ⟩ → ⟨ h-quotient ⟩
      step3-backward = fst step3-backward-hom

      step3-forward-eval : step3-forward-hom ∘cr π-h ≡ π-rec
      step3-forward-eval = QB.evalInduce {B = freeBA ℕ} {f = h} rec-quotient

      step3-backward-eval : step3-backward-hom ∘cr π-rec ≡ π-h
      step3-backward-eval = QB.evalInduce {B = freeBA ℕ} {f = ⊎.rec f g} h-quotient

      step3-backward∘forward-on-π : (x : ⟨ freeBA ℕ ⟩) → step3-backward (step3-forward (fst π-h x)) ≡ fst π-h x
      step3-backward∘forward-on-π x =
        step3-backward (step3-forward (fst π-h x))
          ≡⟨ cong step3-backward (cong (λ hom → fst hom x) step3-forward-eval) ⟩
        step3-backward (fst π-rec x)
          ≡⟨ cong (λ hom → fst hom x) step3-backward-eval ⟩
        fst π-h x ∎

      step3-forward∘backward-on-π : (y : ⟨ freeBA ℕ ⟩) → step3-forward (step3-backward (fst π-rec y)) ≡ fst π-rec y
      step3-forward∘backward-on-π y =
        step3-forward (step3-backward (fst π-rec y))
          ≡⟨ cong step3-forward (cong (λ hom → fst hom y) step3-backward-eval) ⟩
        step3-forward (fst π-h y)
          ≡⟨ cong (λ hom → fst hom y) step3-forward-eval ⟩
        fst π-rec y ∎

      step3-iso : Iso ⟨ h-quotient ⟩ ⟨ rec-quotient ⟩
      Iso.fun step3-iso = step3-forward
      Iso.inv step3-iso = step3-backward
      Iso.sec step3-iso = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = ⊎.rec f g}
        (⟨ rec-quotient ⟩ , BooleanRingStr.is-set (snd rec-quotient)) (funExt step3-forward∘backward-on-π))
      Iso.ret step3-iso = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = h}
        (⟨ h-quotient ⟩ , BooleanRingStr.is-set (snd h-quotient)) (funExt step3-backward∘forward-on-π))

      step3-equiv' : BooleanRingEquiv h-quotient rec-quotient
      step3-equiv' = isoToEquiv step3-iso , snd step3-forward-hom

      target-ring : BooleanRing ℓ-zero
      target-ring = (freeBA ℕ QB./Im f) QB./Im d'

      equiv-hom : BoolHom (fst B) (freeBA ℕ QB./Im f)
      equiv-hom = fst (fst equiv) , snd equiv

      π-d' : BoolHom (freeBA ℕ QB./Im f) target-ring
      π-d' = QB.quotientImageHom

      composite-hom-1 : BoolHom (fst B) target-ring
      composite-hom-1 = π-d' ∘cr equiv-hom

      composite-sends-d-to-0 : (n : ℕ) → composite-hom-1 $cr (d n) ≡ BooleanRingStr.𝟘 (snd target-ring)
      composite-sends-d-to-0 n = QB.zeroOnImage {f = d'} n

      step1-forward-hom : BoolHom B/d target-ring
      step1-forward-hom = QB.inducedHom target-ring composite-hom-1 composite-sends-d-to-0

      π-d : BoolHom (fst B) B/d
      π-d = QB.quotientImageHom

      equiv⁻¹-hom : BoolHom (freeBA ℕ QB./Im f) (fst B)
      equiv⁻¹-hom = fst (fst (invBooleanRingEquiv (fst B) (freeBA ℕ QB./Im f) equiv)) ,
                    snd (invBooleanRingEquiv (fst B) (freeBA ℕ QB./Im f) equiv)

      backward-composite-1 : BoolHom (freeBA ℕ QB./Im f) B/d
      backward-composite-1 = π-d ∘cr equiv⁻¹-hom

      backward-composite-sends-d'-to-0 : (n : ℕ) → backward-composite-1 $cr (d' n) ≡ BooleanRingStr.𝟘 (snd B/d)
      backward-composite-sends-d'-to-0 n =
        π-d $cr (equiv⁻¹-hom $cr (fst (fst equiv) (d n)))
          ≡⟨ cong (π-d $cr_) (Iso.ret (equivToIso (fst equiv)) (d n)) ⟩
        π-d $cr (d n)
          ≡⟨ QB.zeroOnImage {f = d} n ⟩
        BooleanRingStr.𝟘 (snd B/d) ∎

      step1-backward-hom : BoolHom target-ring B/d
      step1-backward-hom = QB.inducedHom B/d backward-composite-1 backward-composite-sends-d'-to-0

      step1-forward-fun : ⟨ B/d ⟩ → ⟨ target-ring ⟩
      step1-forward-fun = fst step1-forward-hom

      step1-backward-fun : ⟨ target-ring ⟩ → ⟨ B/d ⟩
      step1-backward-fun = fst step1-backward-hom

      step1-forward-eval : step1-forward-hom ∘cr π-d ≡ composite-hom-1
      step1-forward-eval = QB.evalInduce {B = fst B} {f = d} target-ring

      step1-backward-eval : step1-backward-hom ∘cr π-d' ≡ backward-composite-1
      step1-backward-eval = QB.evalInduce {B = freeBA ℕ QB./Im f} {f = d'} B/d

      equiv⁻¹∘equiv≡id : (x : ⟨ fst B ⟩) → fst equiv⁻¹-hom (fst (fst equiv) x) ≡ x
      equiv⁻¹∘equiv≡id = Iso.ret (equivToIso (fst equiv))

      equiv∘equiv⁻¹≡id : (y : ⟨ freeBA ℕ QB./Im f ⟩) → fst (fst equiv) (fst equiv⁻¹-hom y) ≡ y
      equiv∘equiv⁻¹≡id = Iso.sec (equivToIso (fst equiv))

      step1-backward∘forward-on-π : (x : ⟨ fst B ⟩) → step1-backward-fun (step1-forward-fun (fst π-d x)) ≡ fst π-d x
      step1-backward∘forward-on-π x =
        step1-backward-fun (step1-forward-fun (fst π-d x))
          ≡⟨ cong step1-backward-fun (cong (λ hom → fst hom x) step1-forward-eval) ⟩
        step1-backward-fun (fst composite-hom-1 x)
          ≡⟨ cong (λ hom → fst hom (fst (fst equiv) x)) step1-backward-eval ⟩
        fst π-d (fst equiv⁻¹-hom (fst (fst equiv) x))
          ≡⟨ cong (fst π-d) (equiv⁻¹∘equiv≡id x) ⟩
        fst π-d x ∎

      step1-forward∘backward-on-π : (y : ⟨ freeBA ℕ QB./Im f ⟩) →
                                     step1-forward-fun (step1-backward-fun (fst π-d' y)) ≡ fst π-d' y
      step1-forward∘backward-on-π y =
        step1-forward-fun (step1-backward-fun (fst π-d' y))
          ≡⟨ cong step1-forward-fun (cong (λ hom → fst hom y) step1-backward-eval) ⟩
        step1-forward-fun (fst backward-composite-1 y)
          ≡⟨ cong (λ hom → fst hom (fst equiv⁻¹-hom y)) step1-forward-eval ⟩
        fst π-d' (fst (fst equiv) (fst equiv⁻¹-hom y))
          ≡⟨ cong (fst π-d') (equiv∘equiv⁻¹≡id y) ⟩
        fst π-d' y ∎

      step1-iso : Iso ⟨ B/d ⟩ ⟨ target-ring ⟩
      Iso.fun step1-iso = step1-forward-fun
      Iso.inv step1-iso = step1-backward-fun
      Iso.sec step1-iso = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ QB./Im f} {f = d'}
        (⟨ target-ring ⟩ , BooleanRingStr.is-set (snd target-ring)) (funExt step1-forward∘backward-on-π))
      Iso.ret step1-iso = funExt⁻ (QB.quotientImageHomEpi {B = fst B} {f = d}
        (⟨ B/d ⟩ , BooleanRingStr.is-set (snd B/d)) (funExt step1-backward∘forward-on-π))

      step1-equiv : BooleanRingEquiv B/d target-ring
      step1-equiv = isoToEquiv step1-iso , snd step1-forward-hom

      step1-equiv' : BooleanRingEquiv B/d ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
      step1-equiv' = subst (λ seq → BooleanRingEquiv B/d ((freeBA ℕ QB./Im f) QB./Im seq))
                       (funExt (λ n → sym (g-is-section n))) step1-equiv

      B'-seq : BooleanRing ℓ-zero
      B'-seq = (freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g)

      invStep2-seq : BooleanRingEquiv B'-seq rec-quotient
      invStep2-seq = invBooleanRingEquiv rec-quotient B'-seq step2-equiv

      invStep3-seq : BooleanRingEquiv rec-quotient h-quotient
      invStep3-seq = invBooleanRingEquiv h-quotient rec-quotient step3-equiv'

      step12-seq : BooleanRingEquiv B/d rec-quotient
      step12-seq = compBoolRingEquiv B/d B'-seq rec-quotient step1-equiv' invStep2-seq

      B/d-equiv : BooleanRingEquiv B/d (freeBA ℕ QB./Im h)
      B/d-equiv = compBoolRingEquiv B/d rec-quotient h-quotient step12-seq invStep3-seq

quotientPreservesBooleω : (α : binarySequence) → ∥ has-Boole-ω' (BoolBR QB./Im α) ∥₁
quotientPreservesBooleω α = quotientBySeqHasBooleω Bool-Booleω α

2/α-Booleω : (α : binarySequence) → Booleω
2/α-Booleω α = (BoolBR QB./Im α) , quotientPreservesBooleω α

mp-from-SD : StoneDualityAxiom → MarkovPrinciple
mp-from-SD SD α α≠0 = MarkovLib.extract' α (MarkovLib.∃αn α (trivialQuotient→1∈I BoolCR (IQ.genIdeal BoolCR α) (sym 0≡1-CR)))
  where
  open import Axioms.StoneDuality using (evaluationMap)
  open import CommRingQuotients.TrivialIdeal using (trivialQuotient→1∈I)
  import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ

  BoolCR = BooleanRing→CommRing BoolBR

  0≡1-BR : BooleanRingStr.𝟘 (snd (BoolBR QB./Im α)) ≡ BooleanRingStr.𝟙 (snd (BoolBR QB./Im α))
  0≡1-BR = SpectrumEmptyImpliesTrivial.0≡1-in-B SD (2/α-Booleω α) (MarkovLib.emptySp α α≠0)

  open import QuotientBool using (_/Im_)
  opaque
    unfolding _/Im_
    0≡1-CR : CommRingStr.0r (snd (BoolCR IQ./Im α)) ≡ CommRingStr.1r (snd (BoolCR IQ./Im α))
    0≡1-CR = 0≡1-BR

postulate
  sd-axiom : StoneDualityAxiom

-- SurjectionsAreFormalSurjections axiom (tex line 294-297)

isInjectiveBoolHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isInjectiveBoolHom B C g = (x y : ⟨ fst B ⟩) → fst g x ≡ fst g y → x ≡ y

isSurjectiveSpHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isSurjectiveSpHom B C g = (h : Sp B) → ∥ Σ[ h' ∈ Sp C ] h' ∘cr g ≡ h ∥₁

SurjectionsAreFormalSurjectionsAxiom : Type (ℓ-suc ℓ-zero)
SurjectionsAreFormalSurjectionsAxiom = (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isInjectiveBoolHom B C g ↔ isSurjectiveSpHom B C g

postulate
  surj-formal-axiom : SurjectionsAreFormalSurjectionsAxiom

injective→Sp-surjective : (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isInjectiveBoolHom B C g → isSurjectiveSpHom B C g
injective→Sp-surjective B C g = fst (surj-formal-axiom B C g)

-- Local Choice axiom (tex line 348-353, AxLocalChoice)

isSurjectiveSpMap : {B C : Booleω} → (Sp C → Sp B) → Type ℓ-zero
isSurjectiveSpMap {B} {C} q = (h : Sp B) → ∥ Σ[ h' ∈ Sp C ] q h' ≡ h ∥₁

LocalChoiceAxiom : Type (ℓ-suc ℓ-zero)
LocalChoiceAxiom = (B : Booleω) (P : Sp B → Type ℓ-zero)
  → ((s : Sp B) → ∥ P s ∥₁)
  → ∥ Σ[ C ∈ Booleω ] Σ[ q ∈ (Sp C → Sp B) ]
      (isSurjectiveSpMap {B} {C} q × ((t : Sp C) → P (q t))) ∥₁

postulate
  localChoice-axiom : LocalChoiceAxiom

mp : MarkovPrinciple
mp = mp-from-SD sd-axiom

∞ : ℕ∞
∞ = (λ _ → false) , (λ m n αm=t _ → ex-falso (false≢true αm=t))

-- Markov principle for ℕ∞ elements (tex Theorem after NotWLPO, line 500)
ℕ∞-Markov : (α : ℕ∞) → ¬ ((n : ℕ) → fst α n ≡ false) → Σ[ n ∈ ℕ ] fst α n ≡ true
ℕ∞-Markov α = mp (fst α)

data Reveal_·_is_ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) (y : B x) : Type₀ where
  [_] : f x ≡ y → Reveal f · x is y

inspect : ∀ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) → Reveal f · x is (f x)
inspect f x = [ refl ]

open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

cantorPair : ℕ → ℕ → ℕ
cantorPair m n = Iso.fun ℕ×ℕ≅ℕ (m , n)

cantorUnpair : ℕ → ℕ × ℕ
cantorUnpair = Iso.inv ℕ×ℕ≅ℕ

cantorUnpair-pair : (m n : ℕ) → cantorUnpair (cantorPair m n) ≡ (m , n)
cantorUnpair-pair m n = Iso.ret ℕ×ℕ≅ℕ (m , n)

openAnd : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
        → isOpenProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
openAnd P Q Popen Qopen = PT.rec2 squash₁ go Popen Qopen
  where
  go : isOpenWitness P → isOpenWitness Q
     → isOpenProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
  go (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) = ∣ γ , forward , backward ∣₁
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
          αn=t : α n ≡ true
          αn=t = and-true-left (α n) (β m) γk=t
          βm=t : β m ≡ true
          βm=t = and-true-right (α n) (β m) γk=t
      in (∃α→P (n , αn=t)) , (∃β→Q (m , βm=t))
      where
      and-true-left : (a b : Bool) → a and b ≡ true → a ≡ true
      and-true-left true  _ _ = refl
      and-true-left false _ p = ex-falso (false≢true p)

      and-true-right : (a b : Bool) → a and b ≡ true → b ≡ true
      and-true-right true  _ p = p
      and-true-right false _ p = ex-falso (false≢true p)

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

firstTrue-false-but-original-true : (α : binarySequence) (n : ℕ)
                                   → firstTrue α n ≡ false → α n ≡ true
                                   → Σ[ m ∈ ℕ ] (suc m ≤ n) × (α m ≡ true)
firstTrue-false-but-original-true α zero ft0=f α0=t = ex-falso (true≢false (sym α0=t ∙ ft0=f))
firstTrue-false-but-original-true α (suc n) ft-sn=f α-sn=t with α zero | inspect α zero
... | true  | [ α0=t ] = zero , suc-≤-suc zero-≤ , α0=t
... | false | _ =
  let (m , m<n , αsm=t) = firstTrue-false-but-original-true (α ∘ suc) n ft-sn=f α-sn=t
  in suc m , suc-≤-suc m<n , αsm=t

closedCountableIntersection : (P : ℕ → hProp ℓ-zero)
                            → ((n : ℕ) → isClosedProp (P n))
                            → isClosedProp (((n : ℕ) → ⟨ P n ⟩) , isPropΠ (λ n → snd (P n)))
closedCountableIntersection P αs =
  PT.rec squash₁ go (countableChoice _ αs)
  where
  go : ((n : ℕ) → Σ[ α ∈ binarySequence ] ⟨ P n ⟩ ↔ ((k : ℕ) → α k ≡ false))
     → isClosedProp (((n : ℕ) → ⟨ P n ⟩) , isPropΠ (λ n → snd (P n)))
  go αs-bare = ∣ β , forward , backward ∣₁
    where
    αP : ℕ → binarySequence
    αP n = fst (αs-bare n)

    β : binarySequence
    β k = let (m , n) = cantorUnpair k in αP m n

    forward : ((n : ℕ) → ⟨ P n ⟩) → (k : ℕ) → β k ≡ false
    forward allP k =
      let (m , n) = cantorUnpair k
          Pm→allFalse = fst (snd (αs-bare m))
      in Pm→allFalse (allP m) n

    backward : ((k : ℕ) → β k ≡ false) → (n : ℕ) → ⟨ P n ⟩
    backward allβFalse n = snd (snd (αs-bare n)) allαnFalse
      where
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
openCountableUnion P αs = PT.rec squash₁ go (countableChoice _ αs)
  where
  go : ((n : ℕ) → isOpenWitness (P n))
     → isOpenProp (∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁ , squash₁)
  go αs-bare = ∣ β , forward , backward ∣₁
    where
    αP : ℕ → binarySequence
    αP n = fst (αs-bare n)

    β : binarySequence
    β k = let (m , n) = cantorUnpair k in αP m n

    backward : Σ[ k ∈ ℕ ] β k ≡ true → ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁
    backward (k , βk=t) = let (n , m) = cantorUnpair k in ∣ n , snd (snd (αs-bare n)) (m , βk=t) ∣₁

    forward : ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁ → Σ[ k ∈ ℕ ] β k ≡ true
    forward truncExists = mp β ¬allFalse
      where
      ¬allFalse : ¬ ((k : ℕ) → β k ≡ false)
      ¬allFalse allFalse = PT.rec isProp⊥ helper truncExists
        where
        helper : Σ[ n ∈ ℕ ] ⟨ P n ⟩ → ⊥
        helper (n , pn) =
          let Pn→exists = fst (snd (αs-bare n))
              (m , αnm=t) = Pn→exists pn
              k = cantorPair n m
              βk=t : β k ≡ true
              βk=t =
                αP (fst (cantorUnpair k)) (snd (cantorUnpair k))
                  ≡⟨ cong (λ p → αP (fst p) (snd p)) (cantorUnpair-pair n m) ⟩
                αP n m
                  ≡⟨ αnm=t ⟩
                true ∎
          in false≢true (sym (allFalse k) ∙ βk=t)

-- (ClopenDecidable from tex Corollary 774)

clopenIsDecidable : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp P → Dec ⟨ P ⟩
clopenIsDecidable P Popen Pclosed = PT.rec (isPropDec (snd P)) go Pclosed
  where
  go : Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) → α n ≡ false) → Dec ⟨ P ⟩
  go (α , P→∀ , ∀→P) =
    let ¬P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩
        ¬Popen = negClosedIsOpen mp P α (P→∀ , ∀→P)
        P∨¬P-trunc = (∥ ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩) ∥₁) , squash₁
        P∨¬P-trunc-open = openOrMP mp P ¬P Popen ¬Popen
    in ⊎.rec yes no (PT.rec (isProp⊎ (snd P) (isProp¬ ⟨ P ⟩) (λ p ¬p → ¬p p)) (λ x → x)
         (openIsStable mp P∨¬P-trunc P∨¬P-trunc-open
           (λ k → k ∣ inr (λ p → k ∣ inl p ∣₁) ∣₁)))

-- (ImplicationOpenClosed from tex Lemma 857)

implicationOpenClosed : (P Q : hProp ℓ-zero) → isOpenProp P → isClosedProp Q
                      → isClosedProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
implicationOpenClosed P Q Popen Qclosed = PT.rec squash₁ go Qclosed
  where
  go : Σ[ αQ ∈ binarySequence ] ⟨ Q ⟩ ↔ ((n : ℕ) → αQ n ≡ false)
     → isClosedProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
  go (αQ , Q→∀ , ∀→Q) = PT.rec squash₁ go2 ¬P∧¬Qclosed
    where
    P∧¬Qopen : isOpenProp ((⟨ P ⟩ × (¬ ⟨ Q ⟩)) , isProp× (snd P) (isProp¬ ⟨ Q ⟩))
    P∧¬Qopen = openAnd P ((¬ ⟨ Q ⟩) , isProp¬ ⟨ Q ⟩) Popen (negClosedIsOpen mp Q αQ (Q→∀ , ∀→Q))

    ¬P∧¬Qclosed : isClosedProp (¬hProp ((⟨ P ⟩ × (¬ ⟨ Q ⟩)) , isProp× (snd P) (isProp¬ ⟨ Q ⟩)))
    ¬P∧¬Qclosed = negOpenIsClosed ((⟨ P ⟩ × (¬ ⟨ Q ⟩)) , isProp× (snd P) (isProp¬ ⟨ Q ⟩)) P∧¬Qopen

    go2 : Σ[ γ ∈ binarySequence ] (¬ (⟨ P ⟩ × (¬ ⟨ Q ⟩))) ↔ ((n : ℕ) → γ n ≡ false)
        → isClosedProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
    go2 (γ , ¬P∧¬Q→∀ , ∀→¬P∧¬Q) = ∣ γ , forward , backward ∣₁
      where
      forward : (⟨ P ⟩ → ⟨ Q ⟩) → (n : ℕ) → γ n ≡ false
      forward p→q = ¬P∧¬Q→∀ (λ (p , ¬q) → ¬q (p→q p))

      backward : ((n : ℕ) → γ n ≡ false) → ⟨ P ⟩ → ⟨ Q ⟩
      backward all-false p =
        closedIsStable (⟨ Q ⟩ , snd Q) Qclosed (λ ¬q → ∀→¬P∧¬Q all-false (p , ¬q))

-- (ClosedMarkov from tex Lemma 807)
closedMarkovTex : (P : ℕ → hProp ℓ-zero) → ((n : ℕ) → isClosedProp (P n))
                → (¬ ((n : ℕ) → ⟨ P n ⟩)) ↔ ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
closedMarkovTex P Pclosed = PT.rec isPropResult go (countableChoice _ Pclosed)
  where
  isPropResult : isProp ((¬ ((n : ℕ) → ⟨ P n ⟩)) ↔ ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁)
  isPropResult = isProp× (isPropΠ (λ _ → squash₁)) (isPropΠ (λ _ → isProp¬ _))

  go : ((n : ℕ) → Σ[ α ∈ binarySequence ] ⟨ P n ⟩ ↔ ((k : ℕ) → α k ≡ false))
     → (¬ ((n : ℕ) → ⟨ P n ⟩)) ↔ ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
  go bareWitnesses = forward , backward
    where
    ∃¬P-open : isOpenProp (∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ , squash₁)
    ∃¬P-open = openCountableUnion (λ n → (¬ ⟨ P n ⟩) , isProp¬ _)
      (λ n → let (αn , iff) = bareWitnesses n in negClosedIsOpen mp (P n) αn iff)

    forward : ¬ ((n : ℕ) → ⟨ P n ⟩) → ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
    forward ¬∀P = openIsStable mp (∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ , squash₁) ∃¬P-open
      (λ k → ¬∀P (λ n → closedIsStable (P n) (Pclosed n) (λ ¬Pn → k ∣ n , ¬Pn ∣₁)))

    backward : ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ → ¬ ((n : ℕ) → ⟨ P n ⟩)
    backward = PT.rec (isProp¬ _) (λ { (n , ¬Pn) ∀P → ¬Pn (∀P n) })

openSigmaDecidable : (D : hProp ℓ-zero) → Dec ⟨ D ⟩
                   → (Q : ⟨ D ⟩ → hProp ℓ-zero) → ((d : ⟨ D ⟩) → isOpenProp (Q d))
                   → isOpenProp (∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ , squash₁)
openSigmaDecidable D (yes d) Q Qopen = PT.rec squash₁ go (Qopen d)
  where
  go : isOpenWitness (Q d) → isOpenProp (∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ , squash₁)
  go (α , Qd→∃ , ∃→Qd) = ∣ α , forward , backward ∣₁
    where
    forward : ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁ → Σ[ n ∈ ℕ ] α n ≡ true
    forward truncExists = mp α (λ allFalse → PT.rec isProp⊥
      (λ (d' , q) → let (n , αn=t) = Qd→∃ (subst (λ x → ⟨ Q x ⟩) (snd D d' d) q)
        in false≢true (sym (allFalse n) ∙ αn=t)) truncExists)

    backward : Σ[ n ∈ ℕ ] α n ≡ true → ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁
    backward w = ∣ d , ∃→Qd w ∣₁

openSigmaDecidable D (no ¬d) Q Qopen = ∣ (λ _ → false) , forward , backward ∣₁
  where
  forward : ∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ → Σ[ n ∈ ℕ ] false ≡ true
  forward x = ex-falso (PT.rec isProp⊥ (λ { (d , _) → ¬d d }) x)

  backward : Σ[ n ∈ ℕ ] false ≡ true → ∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁
  backward (_ , p) = ex-falso (false≢true p)

-- Open propositions are closed under Σ-types (tex Corollary OpenDependentSums 1313)

openSigmaOpen : (P : hProp ℓ-zero) → isOpenProp P
              → (Q : ⟨ P ⟩ → hProp ℓ-zero) → ((p : ⟨ P ⟩) → isOpenProp (Q p))
              → isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
openSigmaOpen P Popen Q Qopen = PT.rec squash₁ go Popen
  where
  go : isOpenWitness P → isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
  go (α , P→∃ , ∃→P) = PT.rec squash₁ go-union (openCountableUnion Rn Rn-open)
    where
    witness : (n : ℕ) → (α n ≡ true) → ⟨ P ⟩
    witness n = λ eq → ∃→P (n , eq)

    Rn : ℕ → hProp ℓ-zero
    Rn n = (∥ Σ[ eq ∈ (α n ≡ true) ] ⟨ Q (witness n eq) ⟩ ∥₁) , squash₁

    Rn-open : (n : ℕ) → isOpenProp (Rn n)
    Rn-open n = openSigmaDecidable ((α n ≡ true) , isSetBool _ _) (α n =B true)
                  (λ eq → Q (witness n eq))
                  (λ eq → Qopen (witness n eq))

    go-union : isOpenWitness (∥ Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ ∥₁ , squash₁)
             → isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
    go-union (β , union→∃ , ∃→union) = ∣ β ,
       (λ sigPQ → union→∃ (PT.rec squash₁
         (λ (p , qp) → let n = fst (P→∃ p) ; αn=t = snd (P→∃ p)
           in ∣ n , ∣ αn=t , subst (λ x → ⟨ Q x ⟩) (snd P p (witness n αn=t)) qp ∣₁ ∣₁)
         sigPQ)) ,
       (λ w → PT.rec squash₁ (λ (n , rn) →
         PT.rec squash₁ (λ (αn=t , qw) → ∣ witness n αn=t , qw ∣₁) rn) (∃→union w)) ∣₁

openEquiv : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩)
          → isOpenProp P → isOpenProp Q
openEquiv P Q P→Q Q→P Popen =
  PT.map (λ (α , P→∃ , ∃→P) → α , (λ q → P→∃ (Q→P q)) , (λ w → P→Q (∃→P w))) Popen

closedEquiv : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩)
            → isClosedProp P → isClosedProp Q
closedEquiv P Q P→Q Q→P Pclosed =
  PT.map (λ (α , P→∀ , ∀→P) → α , (λ q → P→∀ (Q→P q)) , (λ w → P→Q (∀→P w))) Pclosed

-- Definition (tex line 884-886):

isOpenSubset : {T : Type₀} → (A : T → hProp ℓ-zero) → Type₀
isOpenSubset {T} A = (t : T) → isOpenProp (A t)

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

