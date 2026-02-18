{-# OPTIONS --cubical --guardedness #-}

-- tex Corollary 1613, 1628; Corollary 415; Definition 918, Lemma 1336
-- ClosedPropAsSpectrum, ClosedPropIffStone, TruncationStoneClosed,
-- LemSurjectionsFormalToCompleteness, ODiscInfrastructure, SDDecToElem

module SSD.StoneDuality.ClosedPropSpectrum where

open import SSD.StoneDuality.StoneExamples public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv using (_≃_; invEq; propBiimpl→Equiv; compEquiv; secEq; invEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Nullary.Properties using (isProp¬)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; squash₁)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.BooleanRing.Initial using (BoolBR→)
open import Cubical.Foundations.HLevels using (isPropΠ; hProp; TypeOfHLevel≡; isOfHLevelRespectEquiv)
import SSD.Library.QuotientBool as QB
open import SSD.Library.StoneDuality using (Booleω; Sp; hasStoneStr; Stone; StoneDualityAxiom; evaluationMap; SDHomVersion; isPropHasStoneStr)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import SSD.Library.PresentedBoole using (idBoolHom)

-- ClosedPropAsSpectrum (axiom-free)

module ClosedPropAsSpectrum where

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

    αn-is-false : (b : Bool) → α n ≡ b → b ≡ false
    αn-is-false false _ = refl
    αn-is-false true αn≡true = ex-falso (true≢false chain)
      where
      open BooleanRingStr (snd (BoolBR-quotient α)) using () renaming (𝟘 to 𝟘Q ; 𝟙 to 𝟙Q)
      chain : true ≡ false
      chain =
        true
          ≡⟨ sym h-pres1 ⟩
        fst h 𝟙Q
          ≡⟨ cong (fst h) (sym (IsCommRingHom.pres1 (snd QB.quotientImageHom))) ⟩
        fst h (π true)
          ≡⟨ cong (λ x → fst h (π x)) (sym αn≡true) ⟩
        fst h (π (α n))
          ≡⟨ cong (fst h) (QB.zeroOnImage {B = BoolBR} {f = α} n) ⟩
        fst h 𝟘Q
          ≡⟨ h-pres0 ⟩
        false ∎

  closedPropAsSpectrum : (α : binarySequence)
                       → ((n : ℕ) → α n ≡ false) ↔ BoolHom (BoolBR-quotient α) BoolBR
  closedPropAsSpectrum α = all-false→Sp α , Sp→all-false α

-- TruncationStoneClosed base (axiom-free, tex Corollary 1613 partial)

module TruncationStoneClosed where
  0=1→¬Sp : (B : Booleω) → BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B))
           → ¬ Sp B
  0=1→¬Sp B 0≡1 h = true≢false chain
    where
    open BooleanRingStr (snd (fst B)) renaming (𝟘 to 𝟘B ; 𝟙 to 𝟙B)
    open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)
    chain : true ≡ false
    chain =
      true
        ≡⟨ sym h-pres1 ⟩
      fst h 𝟙B
        ≡⟨ cong (fst h) (sym 0≡1) ⟩
      fst h 𝟘B
        ≡⟨ h-pres0 ⟩
      false ∎

-- All axiom-dependent parts

module WithAxiomsCPS (axioms : Axioms) where
  open WithAxioms axioms

  -- tex Corollary 1628: PropositionsClosedIffStone
  module ClosedPropIffStone where
    open ClosedPropAsSpectrum

    closedProp→hasStoneStr : (P : hProp ℓ-zero) → isClosedProp P → hasStoneStr (fst P)
    closedProp→hasStoneStr P Pclosed = PT.rec (isPropHasStoneStr (Axioms.sd axioms) _) go Pclosed
      where
      go : Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) → α n ≡ false) → hasStoneStr (fst P)
      go (α , P→∀ , ∀→P) = B-quotient-Booleω , sym (ua P≃Sp)
        where
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
        P≃all-false = propBiimpl→Equiv (snd P) isProp-all-false P→∀ ∀→P

        Sp-roundtrip : (h : Sp-quotient) → fst all-false↔Sp (snd all-false↔Sp h) ≡ h
        Sp-roundtrip h = QB.inducedHomUnique {B = BoolBR} {f = α} BoolBR (idBoolHom BoolBR) (snd all-false↔Sp h) h h-comp
          where
          π : ⟨ BoolBR ⟩ → ⟨ B-quotient ⟩
          π = fst QB.quotientImageHom

          open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)
          open IsCommRingHom (snd QB.quotientImageHom) renaming (pres0 to π-pres0 ; pres1 to π-pres1)

          h∘π≡id-pointwise : (b : Bool) → fst h (π b) ≡ b
          h∘π≡id-pointwise false =
            fst h (π false)
              ≡⟨ cong (fst h) π-pres0 ⟩
            fst h (BooleanRingStr.𝟘 (snd B-quotient))
              ≡⟨ h-pres0 ⟩
            false ∎
          h∘π≡id-pointwise true =
            fst h (π true)
              ≡⟨ cong (fst h) π-pres1 ⟩
            fst h (BooleanRingStr.𝟙 (snd B-quotient))
              ≡⟨ h-pres1 ⟩
            true ∎

          h-comp : idBoolHom BoolBR ≡ (h ∘cr QB.quotientImageHom)
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

  -- tex Corollary 415: LemSurjectionsFormalToCompleteness

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
    ¬¬Sp→truncSp B ¬¬SpB = PT.rec squash₁
      (λ pt → PT.rec squash₁ (λ preimg → ∣ fst preimg ∣₁)
        (injective→Sp-surjective Bool-Booleω B (canonical-hom (fst B))
          (canonical-hom-injective (fst B) (¬¬Sp→0≢1 B ¬¬SpB)) pt))
      Sp-Bool-inhabited

    truncSp→¬¬Sp : (B : Booleω) → ∥ Sp B ∥₁ → ¬ ¬ Sp B
    truncSp→¬¬Sp B = PT.rec (isProp¬ _) (λ pt ¬SpB → ¬SpB pt)

    -- tex Corollary 415
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

  -- tex Corollary 1613: TruncationStoneClosedComplete
  module TruncationStoneClosedComplete where
    open ODiscInfrastructure

    ¬Sp-hProp : (B : Booleω) → hProp ℓ-zero
    ¬Sp-hProp B = (¬ Sp B) , isProp¬ (Sp B)

    ¬Sp-isOpen : (B : Booleω) → isOpenProp (¬Sp-hProp B)
    ¬Sp-isOpen B = transport (cong isOpenProp hProp-path)
      (booleω-equality-open B (BooleanRingStr.𝟘 (snd (fst B))) (BooleanRingStr.𝟙 (snd (fst B))))
      where
      0=1-Prop : hProp ℓ-zero
      0=1-Prop = _ , BooleanRingStr.is-set (snd (fst B)) _ _

      hProp-path : 0=1-Prop ≡ ¬Sp-hProp B
      hProp-path = TypeOfHLevel≡ 1 (ua (propBiimpl→Equiv (snd 0=1-Prop) (snd (¬Sp-hProp B))
        (TruncationStoneClosed.0=1→¬Sp B) (SpectrumEmptyImpliesTrivial.0≡1-in-B B)))

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

    TruncationStoneClosed' : (S : Stone) → isClosedProp (∥ fst S ∥₁ , squash₁)
    TruncationStoneClosed' (S , (B , p)) =
      transport (cong (λ X → isClosedProp (∥ X ∥₁ , squash₁)) p) (truncSp-isClosed B)

  -- SDDecToElem: Stone Duality Correspondence (tex AxStoneDuality)
  module SDDecToElemModule where

    DecPredOnSp : (B : Booleω) → Type ℓ-zero
    DecPredOnSp B = Sp B → Bool

    elemFromDecPred : (B : Booleω) → DecPredOnSp B → ⟨ fst B ⟩
    elemFromDecPred B D = invEq (fst (SDHomVersion (Axioms.sd axioms) B)) D

    decPredFromElem-roundtrip : (B : Booleω) (D : DecPredOnSp B)
      → evaluationMap B (elemFromDecPred B D) ≡ D
    decPredFromElem-roundtrip B D = secEq (fst (SDHomVersion (Axioms.sd axioms) B)) D

    decPred-elem-correspondence : (B : Booleω) (D : DecPredOnSp B)
      → let d = elemFromDecPred B D
        in (x : Sp B) → fst x d ≡ D x
    decPred-elem-correspondence B D x =
      cong (λ f → f x) (decPredFromElem-roundtrip B D)
