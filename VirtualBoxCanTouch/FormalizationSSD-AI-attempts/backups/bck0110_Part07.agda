{-# OPTIONS --cubical --guardedness #-}

module work.Part07 where

open import work.Part06 public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv using (_≃_; invEq; propBiimpl→Equiv; compEquiv; secEq)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Nullary.Properties using (isProp¬)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; squash₁)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.BooleanRing.Initial using (BoolBR→)
open import Cubical.Foundations.HLevels using (isPropΠ; hProp; TypeOfHLevel≡)
import QuotientBool as QB
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import CountablyPresentedBooleanRings.PresentedBoole using (idBoolHom)

module ClosedPropAsSpectrum where
  open import Cubical.Algebra.CommRing.Quotient.ImageQuotient

  BoolBR-quotient : binarySequence → BooleanRing ℓ-zero
  BoolBR-quotient α = BoolBR QB./Im α

  all-false→Sp : (α : binarySequence) → ((n : ℕ) → α n ≡ false)
               → BoolHom (BoolBR-quotient α) BoolBR
  all-false→Sp α all-false = QB.inducedHom {B = BoolBR} {f = α} BoolBR (idBoolHom BoolBR) all-false

  Sp→all-false : (α : binarySequence) → BoolHom (BoolBR-quotient α) BoolBR
               → ((n : ℕ) → α n ≡ false)
  Sp→all-false α h n = αn-is-false (α n) refl
    where
    open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)

    π : ⟨ BoolBR ⟩ → ⟨ BoolBR-quotient α ⟩
    π = fst QB.quotientImageHom

    h-π-αn≡0 : fst h (π (α n)) ≡ false
    h-π-αn≡0 = cong (fst h) (QB.zeroOnImage {B = BoolBR} {f = α} n) ∙ h-pres0

    αn-is-false : (b : Bool) → α n ≡ b → b ≡ false
    αn-is-false false _ = refl
    αn-is-false true αn≡true = ex-falso (true≢false contradiction)
      where
      open IsCommRingHom (snd QB.quotientImageHom) renaming (pres1 to π-pres1)

      h-π-αn≡true : fst h (π (α n)) ≡ true
      h-π-αn≡true = cong (λ x → fst h (π x)) αn≡true
                  ∙ cong (fst h) π-pres1
                  ∙ h-pres1

      contradiction : true ≡ false
      contradiction = sym h-π-αn≡true ∙ h-π-αn≡0

  closedPropAsSpectrum : (α : binarySequence)
                       → ((n : ℕ) → α n ≡ false) ↔ BoolHom (BoolBR-quotient α) BoolBR
  closedPropAsSpectrum α = all-false→Sp α , Sp→all-false α

-- PropositionsClosedIffStone (tex Corollary 1628)

module ClosedPropIffStone where
  open import Axioms.StoneDuality using (hasStoneStr; Stone)
  open ClosedPropAsSpectrum

  closedProp→hasStoneStr : (P : hProp ℓ-zero) → isClosedProp P → hasStoneStr (fst P)
  closedProp→hasStoneStr P Pclosed = B-quotient-Booleω , sym (ua P≃Sp)
    where
    α : binarySequence
    α = fst Pclosed

    B-quotient : BooleanRing ℓ-zero
    B-quotient = BoolBR-quotient α

    Sp-quotient : Type ℓ-zero
    Sp-quotient = BoolHom B-quotient BoolBR

    all-false↔Sp : ((n : ℕ) → α n ≡ false) ↔ Sp-quotient
    all-false↔Sp = closedPropAsSpectrum α

    B-quotient-Booleω : Booleω
    B-quotient-Booleω = B-quotient , quotientPreservesBooleω α

    all-false-type : Type ℓ-zero
    all-false-type = (n : ℕ) → α n ≡ false

    isProp-all-false : isProp all-false-type
    isProp-all-false = isPropΠ (λ n → isSetBool (α n) false)

    P≃all-false : fst P ≃ all-false-type
    P≃all-false = propBiimpl→Equiv (snd P) isProp-all-false (fst (snd Pclosed)) (snd (snd Pclosed))

    Sp-roundtrip : (h : Sp-quotient) → fst all-false↔Sp (snd all-false↔Sp h) ≡ h
    Sp-roundtrip h = QB.inducedHomUnique {B = BoolBR} {f = α} BoolBR id-hom (snd all-false↔Sp h) h h-comp
      where
      id-hom : BoolHom BoolBR BoolBR
      id-hom = idBoolHom BoolBR

      π : ⟨ BoolBR ⟩ → ⟨ B-quotient ⟩
      π = fst QB.quotientImageHom

      open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)
      open IsCommRingHom (snd QB.quotientImageHom) renaming (pres0 to π-pres0 ; pres1 to π-pres1)

      h∘π≡id-pointwise : (b : Bool) → fst h (π b) ≡ b
      h∘π≡id-pointwise false = cong (fst h) π-pres0 ∙ h-pres0
      h∘π≡id-pointwise true = cong (fst h) π-pres1 ∙ h-pres1

      h-comp : id-hom ≡ (h ∘cr QB.quotientImageHom)
      h-comp = Σ≡Prop (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing BoolBR)) f
                                                  (snd (BooleanRing→CommRing BoolBR)))
                      (sym (funExt h∘π≡id-pointwise))

    isProp-Sp-quotient : isProp Sp-quotient
    isProp-Sp-quotient h₁ h₂ =
      let all-f₁ = snd all-false↔Sp h₁
          all-f₂ = snd all-false↔Sp h₂
          all-f-eq : all-f₁ ≡ all-f₂
          all-f-eq = isProp-all-false all-f₁ all-f₂
      in h₁                                    ≡⟨ sym (Sp-roundtrip h₁) ⟩
         fst all-false↔Sp all-f₁               ≡⟨ cong (fst all-false↔Sp) all-f-eq ⟩
         fst all-false↔Sp all-f₂               ≡⟨ Sp-roundtrip h₂ ⟩
         h₂                                    ∎

    all-false≃Sp : all-false-type ≃ Sp-quotient
    all-false≃Sp = propBiimpl→Equiv isProp-all-false isProp-Sp-quotient
                    (fst all-false↔Sp) (snd all-false↔Sp)

    P≃Sp : fst P ≃ Sp-quotient
    P≃Sp = compEquiv P≃all-false all-false≃Sp

-- TruncationStoneClosed (tex Corollary 1613)

module TruncationStoneClosed where
  0=1→¬Sp : (B : Booleω) → BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B))
           → ¬ Sp B
  0=1→¬Sp B 0≡1 h = true≢false (sym h-pres1 ∙ cong (fst h) (sym 0≡1) ∙ h-pres0)
    where
    open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)

-- LemSurjectionsFormalToCompleteness (tex Corollary 415)

module LemSurjectionsFormalToCompleteness where

  ¬¬Sp→0≢1 : (B : Booleω) → ¬ ¬ Sp B → ¬ (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
  ¬¬Sp→0≢1 B ¬¬SpB 0≡1 = ¬¬SpB (TruncationStoneClosed.0=1→¬Sp B 0≡1)

  canonical-hom : (B : BooleanRing ℓ-zero) → BoolHom BoolBR B
  canonical-hom B = BoolBR→ B

  canonical-hom-injective : (B : BooleanRing ℓ-zero)
    → ¬ (BooleanRingStr.𝟘 (snd B) ≡ BooleanRingStr.𝟙 (snd B))
    → (b₁ b₂ : Bool) → fst (canonical-hom B) b₁ ≡ fst (canonical-hom B) b₂ → b₁ ≡ b₂
  canonical-hom-injective B 0≢1 false false _ = refl
  canonical-hom-injective B 0≢1 false true  p = ex-falso (0≢1 p)
  canonical-hom-injective B 0≢1 true  false p = ex-falso (0≢1 (sym p))
  canonical-hom-injective B 0≢1 true  true  _ = refl

  ¬¬Sp→truncSp : (B : Booleω) → ¬ ¬ Sp B → ∥ Sp B ∥₁
  ¬¬Sp→truncSp B ¬¬SpB = PT.rec squash₁ step1 Sp-Bool-inhabited
    where
    surj : isSurjectiveSpHom Bool-Booleω B (canonical-hom (fst B))
    surj = injective→Sp-surjective Bool-Booleω B (canonical-hom (fst B))
             (canonical-hom-injective (fst B) (¬¬Sp→0≢1 B ¬¬SpB))

    step1 : Sp Bool-Booleω → ∥ Sp B ∥₁
    step1 pt = PT.rec squash₁ (λ preimg → ∣ fst preimg ∣₁) (surj pt)

  truncSp→¬¬Sp : (B : Booleω) → ∥ Sp B ∥₁ → ¬ ¬ Sp B
  truncSp→¬¬Sp B = PT.rec (isProp¬ _) (λ pt ¬SpB → ¬SpB pt)

  -- This is tex Corollary 415 (LemSurjectionsFormalToCompleteness)
  LemSurjectionsFormalToCompleteness-derived : (B : Booleω)
    → ⟨ ¬hProp ((¬ Sp B) , isProp¬ (Sp B)) ⟩ ≃ ∥ Sp B ∥₁
  LemSurjectionsFormalToCompleteness-derived B =
    propBiimpl→Equiv
      (isProp¬ (¬ Sp B))
      squash₁
      (¬¬Sp→truncSp B)
      (truncSp→¬¬Sp B)

-- ODisc Infrastructure (tex Definition 918, Lemma 1336)
module ODiscInfrastructure where
  postulate
    booleω-equality-open : (B : Booleω) → (a b : ⟨ fst B ⟩)
      → isOpenProp ((a ≡ b) , BooleanRingStr.is-set (snd (fst B)) a b)

  0=1-isOpen : (B : Booleω)
    → isOpenProp ((BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
                 , BooleanRingStr.is-set (snd (fst B)) _ _)
  0=1-isOpen B = booleω-equality-open B (BooleanRingStr.𝟘 (snd (fst B)))
                                        (BooleanRingStr.𝟙 (snd (fst B)))

-- TruncationStoneClosed completion (tex Corollary 1613)

module TruncationStoneClosedComplete where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open ODiscInfrastructure

  ¬Sp-hProp : (B : Booleω) → hProp ℓ-zero
  ¬Sp-hProp B = (¬ Sp B) , isProp¬ (Sp B)

  ¬Sp-isOpen : (B : Booleω) → isOpenProp (¬Sp-hProp B)
  ¬Sp-isOpen B = transport (cong isOpenProp hProp-path) (0=1-isOpen B)
    where
    0=1-Prop : hProp ℓ-zero
    0=1-Prop = _ , BooleanRingStr.is-set (snd (fst B)) _ _

    hProp-path : 0=1-Prop ≡ ¬Sp-hProp B
    hProp-path = TypeOfHLevel≡ 1 (ua (propBiimpl→Equiv (snd 0=1-Prop) (snd (¬Sp-hProp B))
      (TruncationStoneClosed.0=1→¬Sp B) (SpectrumEmptyImpliesTrivial.0≡1-in-B sd-axiom B)))

  ¬¬Sp-hProp : (B : Booleω) → hProp ℓ-zero
  ¬¬Sp-hProp B = ¬hProp (¬Sp-hProp B)

  ¬¬Sp-isClosed : (B : Booleω) → isClosedProp (¬¬Sp-hProp B)
  ¬¬Sp-isClosed B = negOpenIsClosed (¬Sp-hProp B) (¬Sp-isOpen B)

  truncSp-isClosed : (B : Booleω) → isClosedProp (∥ Sp B ∥₁ , squash₁)
  truncSp-isClosed B = transport (cong isClosedProp hProp-path) (¬¬Sp-isClosed B)
    where
    hProp-path : ¬¬Sp-hProp B ≡ (∥ Sp B ∥₁ , squash₁)
    hProp-path = TypeOfHLevel≡ 1
      (ua (LemSurjectionsFormalToCompleteness.LemSurjectionsFormalToCompleteness-derived B))

  TruncationStoneClosed : (S : Stone) → isClosedProp (∥ fst S ∥₁ , squash₁)
  TruncationStoneClosed (S , (B , p)) =
    transport (cong (λ X → isClosedProp (∥ X ∥₁ , squash₁)) p) (truncSp-isClosed B)

-- SDDecToElem: Stone Duality Correspondence (tex AxStoneDuality)

module SDDecToElemModule where
  open import Axioms.StoneDuality using (evaluationMap; StoneDualityAxiom; SDHomVersion)

  DecPredOnSp : (B : Booleω) → Type ℓ-zero
  DecPredOnSp B = Sp B → Bool

  elemFromDecPred : StoneDualityAxiom → (B : Booleω) → DecPredOnSp B → ⟨ fst B ⟩
  elemFromDecPred SD B D = invEq (fst (SDHomVersion SD B)) D

  decPredFromElem-roundtrip : (SD : StoneDualityAxiom) (B : Booleω) (D : DecPredOnSp B)
    → evaluationMap B (elemFromDecPred SD B D) ≡ D
  decPredFromElem-roundtrip SD B D = secEq (fst (SDHomVersion SD B)) D

  decPred-elem-correspondence : (SD : StoneDualityAxiom) (B : Booleω) (D : DecPredOnSp B)
    → let d = elemFromDecPred SD B D
      in (x : Sp B) → fst x d ≡ D x
  decPred-elem-correspondence SD B D x =
    cong (λ f → f x) (decPredFromElem-roundtrip SD B D)

-- StoneEqualityClosed (tex Lemma 1636)
