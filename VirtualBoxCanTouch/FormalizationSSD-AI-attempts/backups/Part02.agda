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
import Cubical.Induction.WellFounded as WF
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

mp : MarkovPrinciple
mp = mp-from-SD sd-axiom

openOr : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
       → isOpenProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
openOr = openOrMP mp

∞ : ℕ∞
∞ = (λ _ → false) , (λ m n αm=t _ → ex-falso (false≢true αm=t))

-- Markov principle for ℕ∞ elements (tex Theorem after NotWLPO, line 500)
ℕ∞-Markov : (α : ℕ∞) → ¬ ((n : ℕ) → fst α n ≡ false) → Σ[ n ∈ ℕ ] fst α n ≡ true
ℕ∞-Markov α = mp (fst α)

postulate
  llpo : LLPO

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

closedDeMorgan : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
               → ¬ ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
closedDeMorgan P Q Pclosed Qclosed ¬¬P∧¬Q =
  let
      δ₀ : binarySequence
      δ₀ = interleave α β

      δ : binarySequence
      δ = firstTrue δ₀

      δ-hamo : hitsAtMostOnce δ
      δ-hamo = firstTrue-hitsAtMostOnce δ₀

      δ∞ : ℕ∞
      δ∞ = δ , δ-hamo

      llpo-result : ∥ ((k : ℕ) → δ (2 ·ℕ k) ≡ false) ⊎ ((k : ℕ) → δ (suc (2 ·ℕ k)) ≡ false) ∥₁
      llpo-result = llpo δ∞

  in PT.rec squash₁ helper llpo-result
  where
  Pclosed-bare = extractClosedProp {P} Pclosed
  α = fst Pclosed-bare
  P→∀α = fst (snd Pclosed-bare)
  ∀α→P = snd (snd Pclosed-bare)
  Qclosed-bare = extractClosedProp {Q} Qclosed
  β = fst Qclosed-bare
  Q→∀β = fst (snd Qclosed-bare)
  ∀β→Q = snd (snd Qclosed-bare)

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
            ex-falso (true≢false (sym (subst (λ x → firstTrue (interleave α β) x ≡ true)
                                        (sym (2·half-even n n-even)) ft-n=t)
                                  ∙ allEvensF (half n)))
    ...   | no n-odd =
            let odd-eq = ¬true→false (isEvenB n) n-odd
            in n , odd-eq , sym (interleave-odd α β n odd-eq) ∙ δ₀-n=t
    find-first-true-odd-step n rec δ₀-n=t allEvensF | no ft-n≠t =
      let (m , m<n , δ₀-m=t) = firstTrue-false-but-original-true (interleave α β) n
                                  (¬true→false (firstTrue (interleave α β) n) ft-n≠t) δ₀-n=t
      in rec m m<n δ₀-m=t allEvensF

    find-first-true-odd : (n : ℕ) → ResultOdd n
    find-first-true-odd = induction find-first-true-odd-step

  allEvensF-implies-P : ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false) → ⟨ P ⟩
  allEvensF-implies-P allEvensF = closedIsStable P Pclosed ¬¬P
    where
    ¬¬P : ¬ ¬ ⟨ P ⟩
    ¬¬P ¬p =
      let (k , αk=t) = mp α (λ all-false → ¬p (∀α→P all-false))
          (m , m-odd , βj=t) = find-first-true-odd (2 ·ℕ k) (interleave-2k α β k ∙ αk=t) allEvensF
      in ¬¬P∧¬Q (¬p , λ q → false≢true (sym (Q→∀β q (half m)) ∙ βj=t))

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
            n , n-even , sym (interleave-even α β n n-even) ∙ δ₀-n=t
    ...   | no n-odd =
            let odd-eq = ¬true→false (isEvenB n) n-odd
            in ex-falso (true≢false (sym (subst (λ x → firstTrue (interleave α β) x ≡ true)
                                           (sym (suc-2·half-odd n odd-eq)) ft-n=t)
                                     ∙ allOddsF (half n)))
    find-first-true-even-step n rec δ₀-n=t allOddsF | no ft-n≠t =
      let (m , m<n , δ₀-m=t) = firstTrue-false-but-original-true (interleave α β) n
                                  (¬true→false (firstTrue (interleave α β) n) ft-n≠t) δ₀-n=t
      in rec m m<n δ₀-m=t allOddsF

    find-first-true-even : (n : ℕ) → ResultEven n
    find-first-true-even = induction find-first-true-even-step

  allOddsF-implies-Q : ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false) → ⟨ Q ⟩
  allOddsF-implies-Q allOddsF = closedIsStable Q Qclosed ¬¬Q
    where
    ¬¬Q : ¬ ¬ ⟨ Q ⟩
    ¬¬Q ¬q =
      let (k , βk=t) = mp β (λ all-false → ¬q (∀β→Q all-false))
          (m , m-even , αj=t) = find-first-true-even (suc (2 ·ℕ k)) (interleave-2k+1 α β k ∙ βk=t) allOddsF
      in ¬¬P∧¬Q ((λ p → false≢true (sym (P→∀α p (half m)) ∙ αj=t)) , ¬q)

  helper : ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false)
         ⊎ ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false)
         → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
  helper (inl allEvensF) = ∣ inl (allEvensF-implies-P allEvensF) ∣₁
  helper (inr allOddsF) = ∣ inr (allOddsF-implies-Q allOddsF) ∣₁

closedOr : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
         → isClosedProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
closedOr P Q Pclosed Qclosed = ∣ γ , forward , backward ∣₁
  where
  ¬P : hProp ℓ-zero
  ¬P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩

  ¬Q : hProp ℓ-zero
  ¬Q = (¬ ⟨ Q ⟩) , isProp¬ ⟨ Q ⟩

  ¬P∧¬Qopen : isOpenProp (((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) , isProp× (isProp¬ ⟨ P ⟩) (isProp¬ ⟨ Q ⟩))
  ¬P∧¬Qopen = openAnd ¬P ¬Q (negClosedIsOpen mp P Pclosed) (negClosedIsOpen mp Q Qclosed)

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

-- (tex line 716)
openDeMorgan : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
             → (¬ (⟨ P ⟩ × ⟨ Q ⟩)) ↔ ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁
openDeMorgan P Q Popen Qopen = forward , backward
  where
  forward : ¬ (⟨ P ⟩ × ⟨ Q ⟩) → ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁
  forward ¬P×Q = closedDeMorgan (¬hProp P) (¬hProp Q) (negOpenIsClosed P Popen) (negOpenIsClosed Q Qopen)
    (λ (¬¬p , ¬¬q) → ¬P×Q (openIsStable mp P Popen ¬¬p , openIsStable mp Q Qopen ¬¬q))

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
closedCountableIntersection P αs = ∣ β , forward , backward ∣₁
  where
  αs-bare : (n : ℕ) → _
  αs-bare n = extractClosedProp {P n} (αs n)

  αP : ℕ → binarySequence
  αP n = fst (αs-bare n)

  β : binarySequence
  β = flatten αP

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
openCountableUnion P αs = β , forward , backward
  where
  αP : ℕ → binarySequence
  αP n = fst (αs n)

  β : binarySequence
  β = flatten αP

  backward : Σ[ k ∈ ℕ ] β k ≡ true → ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁
  backward (k , βk=t) = let (n , m) = cantorUnpair k in ∣ n , snd (snd (αs n)) (m , βk=t) ∣₁

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
              αP (fst (cantorUnpair k)) (snd (cantorUnpair k))
                ≡⟨ cong (λ p → αP (fst p) (snd p)) (cantorUnpair-pair n m) ⟩
              αP n m
                ≡⟨ αnm=t ⟩
              true ∎
        in false≢true (sym (allFalse k) ∙ βk=t)

-- (ClopenDecidable from tex Corollary 774)

clopenIsDecidable : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp P → Dec ⟨ P ⟩
clopenIsDecidable P Popen Pclosed =
  let ¬P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩
      ¬Popen = negClosedIsOpen mp P Pclosed
      P∨¬P-trunc = (∥ ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩) ∥₁) , squash₁
      P∨¬P-trunc-open = openOr P ¬P Popen ¬Popen
  in ⊎.rec yes no (PT.rec (isProp⊎ (snd P) (isProp¬ ⟨ P ⟩) (λ p ¬p → ¬p p)) (λ x → x)
       (openIsStable mp P∨¬P-trunc P∨¬P-trunc-open
         (λ k → k ∣ inr (λ p → k ∣ inl p ∣₁) ∣₁)))

-- (ImplicationOpenClosed from tex Lemma 857)

implicationOpenClosed : (P Q : hProp ℓ-zero) → isOpenProp P → isClosedProp Q
                      → isClosedProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
implicationOpenClosed P Q Popen Qclosed = ∣ γ , forward , backward ∣₁
  where
  P∧¬Qopen : isOpenProp ((⟨ P ⟩ × (¬ ⟨ Q ⟩)) , isProp× (snd P) (isProp¬ ⟨ Q ⟩))
  P∧¬Qopen = openAnd P ((¬ ⟨ Q ⟩) , isProp¬ ⟨ Q ⟩) Popen (negClosedIsOpen mp Q Qclosed)

  ¬P∧¬Q-hProp = ¬hProp ((⟨ P ⟩ × (¬ ⟨ Q ⟩)) , isProp× (snd P) (isProp¬ ⟨ Q ⟩))
  ¬P∧¬Qclosed-bare = extractClosedProp {¬P∧¬Q-hProp}
    (negOpenIsClosed ((⟨ P ⟩ × (¬ ⟨ Q ⟩)) , isProp× (snd P) (isProp¬ ⟨ Q ⟩)) P∧¬Qopen)

  γ = fst ¬P∧¬Qclosed-bare

  forward : (⟨ P ⟩ → ⟨ Q ⟩) → (n : ℕ) → γ n ≡ false
  forward p→q = fst (snd ¬P∧¬Qclosed-bare) (λ (p , ¬q) → ¬q (p→q p))

  backward : ((n : ℕ) → γ n ≡ false) → ⟨ P ⟩ → ⟨ Q ⟩
  backward all-false p =
    closedIsStable (⟨ Q ⟩ , snd Q) Qclosed (λ ¬q → snd (snd ¬P∧¬Qclosed-bare) all-false (p , ¬q))

closedMarkovTex : (P : ℕ → hProp ℓ-zero) → ((n : ℕ) → isClosedProp (P n))
                → (¬ ((n : ℕ) → ⟨ P n ⟩)) ↔ ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
closedMarkovTex P Pclosed = forward , backward
  where
  ∃¬P-open : isOpenProp (∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ , squash₁)
  ∃¬P-open = openCountableUnion (λ n → (¬ ⟨ P n ⟩) , isProp¬ _) (λ n → negClosedIsOpen mp (P n) (Pclosed n))

  forward : ¬ ((n : ℕ) → ⟨ P n ⟩) → ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
  forward ¬∀P = openIsStable mp (∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ , squash₁) ∃¬P-open
    (λ k → ¬∀P (λ n → closedIsStable (P n) (Pclosed n) (λ ¬Pn → k ∣ n , ¬Pn ∣₁)))

  backward : ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ → ¬ ((n : ℕ) → ⟨ P n ⟩)
  backward = PT.rec (isProp¬ _) (λ { (n , ¬Pn) ∀P → ¬Pn (∀P n) })

openSigmaDecidable : (D : hProp ℓ-zero) → Dec ⟨ D ⟩
                   → (Q : ⟨ D ⟩ → hProp ℓ-zero) → ((d : ⟨ D ⟩) → isOpenProp (Q d))
                   → isOpenProp (∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ , squash₁)
openSigmaDecidable D (yes d) Q Qopen = α , forward , backward
  where
  α = Qopen d .fst

  forward : ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁ → Σ[ n ∈ ℕ ] α n ≡ true
  forward truncExists = mp α (λ allFalse → PT.rec isProp⊥
    (λ (d' , q) → let (n , αn=t) = fst (snd (Qopen d)) (subst (λ x → ⟨ Q x ⟩) (snd D d' d) q)
      in false≢true (sym (allFalse n) ∙ αn=t)) truncExists)

  backward : Σ[ n ∈ ℕ ] α n ≡ true → ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁
  backward w = ∣ d , snd (snd (Qopen d)) w ∣₁

openSigmaDecidable D (no ¬d) Q Qopen = ⊥-isOpen .fst , forward , backward
  where
  forward : ∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ → Σ[ n ∈ ℕ ] ⊥-isOpen .fst n ≡ true
  forward x = ex-falso (PT.rec isProp⊥ (λ { (d , _) → ¬d d }) x)

  backward : Σ[ n ∈ ℕ ] ⊥-isOpen .fst n ≡ true → ∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁
  backward (n , αn=t) = ex-falso (true≢false (sym αn=t))

-- Open propositions are closed under Σ-types (tex Corollary OpenDependentSums 1313)

openSigmaOpen : (P : hProp ℓ-zero) → isOpenProp P
              → (Q : ⟨ P ⟩ → hProp ℓ-zero) → ((p : ⟨ P ⟩) → isOpenProp (Q p))
              → isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
openSigmaOpen P (α , P→∃ , ∃→P) Q Qopen = result
  where
  witness : (n : ℕ) → (α n ≡ true) → ⟨ P ⟩
  witness n = λ eq → ∃→P (n , eq)

  Rn : ℕ → hProp ℓ-zero
  Rn n = (∥ Σ[ eq ∈ (α n ≡ true) ] ⟨ Q (witness n eq) ⟩ ∥₁) , squash₁

  Rn-open : (n : ℕ) → isOpenProp (Rn n)
  Rn-open n = openSigmaDecidable ((α n ≡ true) , isSetBool _ _) (α n =B true)
                (λ eq → Q (witness n eq))
                (λ eq → Qopen (witness n eq))

  result : isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
  result =
    let (β , union→∃ , ∃→union) = openCountableUnion Rn Rn-open
    in β ,
       (λ sigPQ → union→∃ (PT.rec squash₁
         (λ (p , qp) → let n = fst (P→∃ p) ; αn=t = snd (P→∃ p)
           in ∣ n , ∣ αn=t , subst (λ x → ⟨ Q x ⟩) (snd P p (witness n αn=t)) qp ∣₁ ∣₁)
         sigPQ)) ,
       (λ w → PT.rec squash₁ (λ (n , rn) →
         PT.rec squash₁ (λ (αn=t , qw) → ∣ witness n αn=t , qw ∣₁) rn) (∃→union w))

openEquiv : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩)
          → isOpenProp P → isOpenProp Q
openEquiv P Q P→Q Q→P (α , P→∃ , ∃→P) =
  α , (λ q → P→∃ (Q→P q)) , (λ w → P→Q (∃→P w))

closedEquiv : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩)
            → isClosedProp P → isClosedProp Q
closedEquiv P Q P→Q Q→P Pclosed =
  let Pclosed-bare = extractClosedProp {P} Pclosed
      α = fst Pclosed-bare
      P→∀ = fst (snd Pclosed-bare)
      ∀→P = snd (snd Pclosed-bare)
  in ∣ α , (λ q → P→∀ (Q→P q)) , (λ w → P→Q (∀→P w)) ∣₁

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

