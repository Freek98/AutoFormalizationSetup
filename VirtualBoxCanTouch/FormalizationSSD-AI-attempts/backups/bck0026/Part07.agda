{-# OPTIONS --cubical --guardedness #-}

module work.Part07 where

open import work.Part06 public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open import Cubical.Foundations.Equiv using (_≃_; equivFun; invEq; propBiimpl→Equiv; compEquiv; retEq; secEq)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; isSetBool; true≢false; false≢true)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no; Discrete→isSet)
open import Cubical.Relation.Nullary.Properties using (isProp¬)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; elim; squash₁; propTruncIdempotent≃)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.BooleanRing.Initial using (BoolBR→; BoolBR→IsUnique)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2; isSetΠ; hProp; isOfHLevelΣ)
import QuotientBool as QB
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; idBoolEquiv; has-Boole-ω')
open import Axioms.StoneDuality using (Booleω; Sp)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty renaming (rec to ex-falso)

module ClosedPropAsSpectrum where
  open import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ

  BoolBR-quotient : binarySequence → BooleanRing ℓ-zero
  BoolBR-quotient α = BoolBR QB./Im α

  all-false→Sp : (α : binarySequence) → ((n : ℕ) → α n ≡ false)
               → BoolHom (BoolBR-quotient α) BoolBR
  all-false→Sp α all-false = QB.inducedHom {B = BoolBR} {f = α} BoolBR id-hom α-to-0
    where
    open import CountablyPresentedBooleanRings.PresentedBoole using (idBoolHom)

    id-hom : BoolHom BoolBR BoolBR
    id-hom = idBoolHom BoolBR

    α-to-0 : (n : ℕ) → id-hom $cr (α n) ≡ BooleanRingStr.𝟘 (snd BoolBR)
    α-to-0 n = all-false n

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
  open import Axioms.StoneDuality using (hasStoneStr; Stone; SpGeneralBooleanRing; isSetSp)
  open ClosedPropAsSpectrum

  closedProp→hasStoneStr : (P : hProp ℓ-zero) → isClosedProp P → hasStoneStr (fst P)
  closedProp→hasStoneStr P Pclosed = Booleω-P , Sp-eq
    where
    α : binarySequence
    α = fst Pclosed

    P→all-false : fst P → ((n : ℕ) → α n ≡ false)
    P→all-false = fst (snd Pclosed)

    all-false→P : ((n : ℕ) → α n ≡ false) → fst P
    all-false→P = snd (snd Pclosed)

    B-quotient : BooleanRing ℓ-zero
    B-quotient = BoolBR-quotient α

    Sp-quotient : Type ℓ-zero
    Sp-quotient = BoolHom B-quotient BoolBR

    all-false↔Sp : ((n : ℕ) → α n ≡ false) ↔ Sp-quotient
    all-false↔Sp = closedPropAsSpectrum α

    P→Sp : fst P → Sp-quotient
    P→Sp p = fst all-false↔Sp (P→all-false p)

    Sp→P : Sp-quotient → fst P
    Sp→P h = all-false→P (snd all-false↔Sp h)

    B-quotient-Booleω : Booleω
    B-quotient-Booleω = B-quotient , quotientPreservesBooleω α

    isPropP : isProp (fst P)
    isPropP = snd P

    isSetSp-quotient : isSet Sp-quotient
    isSetSp-quotient = isSetSp B-quotient

    all-false-type : Type ℓ-zero
    all-false-type = (n : ℕ) → α n ≡ false

    isProp-all-false : isProp all-false-type
    isProp-all-false = isPropΠ (λ n → isSetBool (α n) false)

    P≃all-false : fst P ≃ all-false-type
    P≃all-false = propBiimpl→Equiv isPropP isProp-all-false P→all-false all-false→P

    Sp-roundtrip : (h : Sp-quotient) → fst all-false↔Sp (snd all-false↔Sp h) ≡ h
    Sp-roundtrip h = QB.inducedHomUnique {B = BoolBR} {f = α} BoolBR id-hom α-to-0 h h-comp
      where
      open import CountablyPresentedBooleanRings.PresentedBoole using (idBoolHom)

      id-hom : BoolHom BoolBR BoolBR
      id-hom = idBoolHom BoolBR

      all-false-from-h : (n : ℕ) → α n ≡ false
      all-false-from-h = snd all-false↔Sp h

      α-to-0 : (n : ℕ) → id-hom $cr (α n) ≡ BooleanRingStr.𝟘 (snd BoolBR)
      α-to-0 n = all-false-from-h n

      π : ⟨ BoolBR ⟩ → ⟨ B-quotient ⟩
      π = fst QB.quotientImageHom

      open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)
      open IsCommRingHom (snd QB.quotientImageHom) renaming (pres0 to π-pres0 ; pres1 to π-pres1)

      h∘π-on-false : fst h (π false) ≡ false
      h∘π-on-false = cong (fst h) π-pres0 ∙ h-pres0

      h∘π-on-true : fst h (π true) ≡ true
      h∘π-on-true = cong (fst h) π-pres1 ∙ h-pres1

      h∘π≡id-pointwise : (b : Bool) → fst h (π b) ≡ b
      h∘π≡id-pointwise false = h∘π-on-false
      h∘π≡id-pointwise true = h∘π-on-true

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

    Booleω-P : Booleω
    Booleω-P = B-quotient-Booleω

    Sp-eq : Sp Booleω-P ≡ fst P
    Sp-eq = sym (ua P≃Sp)

  closedProp→Stone : (P : hProp ℓ-zero) → isClosedProp P → Stone
  closedProp→Stone P Pclosed = fst P , closedProp→hasStoneStr P Pclosed

-- TruncationStoneClosed (tex Corollary 1613)
-- 2. 0=1 is open (because B is overtly discrete - tex BooleIsODisc)

module TruncationStoneClosed where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; SpGeneralBooleanRing)

  0=1→¬Sp : (B : Booleω) → BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B))
           → ¬ Sp B
  0=1→¬Sp B 0≡1 h = true≢false (sym h-pres1 ∙ cong (fst h) (sym 0≡1) ∙ h-pres0)
    where
    open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)

-- LemSurjectionsFormalToCompleteness (tex Corollary 415)
-- 4. By SurjectionsAreFormalSurjections (tex Prop 353), Sp(B) → Sp(2) is surjective

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

  canonical-hom-is-injective : (B : Booleω)
    → ¬ (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
    → isInjectiveBoolHom Bool-Booleω B (canonical-hom (fst B))
  canonical-hom-is-injective B 0≢1 b₁ b₂ = canonical-hom-injective (fst B) 0≢1 b₁ b₂

  Sp-canonical-surjective : (B : Booleω)
    → ¬ (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
    → isSurjectiveSpHom Bool-Booleω B (canonical-hom (fst B))
  Sp-canonical-surjective B 0≢1 =
    injective→Sp-surjective Bool-Booleω B (canonical-hom (fst B)) (canonical-hom-is-injective B 0≢1)

  ¬¬Sp→truncSp : (B : Booleω) → ¬ ¬ Sp B → ∥ Sp B ∥₁
  ¬¬Sp→truncSp B ¬¬SpB = PT.rec squash₁ step1 Sp-Bool-inhabited
    where
    0≢1 : ¬ (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
    0≢1 = ¬¬Sp→0≢1 B ¬¬SpB

    surj : isSurjectiveSpHom Bool-Booleω B (canonical-hom (fst B))
    surj = Sp-canonical-surjective B 0≢1

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
-- - Equality in ODisc types is open (tex Lemma 1336 OdiscQuotientCountableByOpen)
-- - Booleω algebras are ODisc (tex Lemma 1396 BooleIsODisc)

module ODiscInfrastructure where
  open import Cubical.Data.Sequence using (Sequence)
  open import Cubical.HITs.SequentialColimit.Base using (SeqColim; incl; push)

  postulate
    booleω-equality-open : (B : Booleω) → (a b : ⟨ fst B ⟩)
      → isOpenProp ((a ≡ b) , BooleanRingStr.is-set (snd (fst B)) a b)

  0=1-isOpen : (B : Booleω)
    → isOpenProp ((BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
                 , BooleanRingStr.is-set (snd (fst B)) _ _)
  0=1-isOpen B = booleω-equality-open B (BooleanRingStr.𝟘 (snd (fst B)))
                                        (BooleanRingStr.𝟙 (snd (fst B)))

  ¬-of-open-is-closed : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp (¬hProp P)
  ¬-of-open-is-closed = negOpenIsClosed

  0≢1-isClosed : (B : Booleω)
    → isClosedProp (¬hProp ((BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
                          , BooleanRingStr.is-set (snd (fst B)) _ _))
  0≢1-isClosed B = ¬-of-open-is-closed
    ((BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
    , BooleanRingStr.is-set (snd (fst B)) _ _)
    (0=1-isOpen B)

-- TruncationStoneClosed completion (tex Corollary 1613)

module TruncationStoneClosedComplete where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; SpGeneralBooleanRing)
  open ODiscInfrastructure

  ¬Sp-hProp : (B : Booleω) → hProp ℓ-zero
  ¬Sp-hProp B = (¬ Sp B) , isProp¬ (Sp B)

  ¬Sp-isOpen : (B : Booleω) → isOpenProp (¬Sp-hProp B)
  ¬Sp-isOpen B = transport (cong isOpenProp hProp-path) (0=1-isOpen B)
    where
    0=1-Prop : hProp ℓ-zero
    0=1-Prop = (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
             , BooleanRingStr.is-set (snd (fst B)) _ _

    fwd : ⟨ 0=1-Prop ⟩ → ⟨ ¬Sp-hProp B ⟩
    fwd = TruncationStoneClosed.0=1→¬Sp B

    bwd : ⟨ ¬Sp-hProp B ⟩ → ⟨ 0=1-Prop ⟩
    bwd spEmpty = SpectrumEmptyImpliesTrivial.0≡1-in-B sd-axiom B spEmpty

    equiv : ⟨ 0=1-Prop ⟩ ≃ ⟨ ¬Sp-hProp B ⟩
    equiv = propBiimpl→Equiv (snd 0=1-Prop) (snd (¬Sp-hProp B)) fwd bwd

    fst-path : fst 0=1-Prop ≡ fst (¬Sp-hProp B)
    fst-path = ua equiv

    hProp-path : 0=1-Prop ≡ ¬Sp-hProp B
    hProp-path = Σ≡Prop {B = λ A → isProp A} (λ _ → isPropIsProp) fst-path

  ¬¬Sp-hProp : (B : Booleω) → hProp ℓ-zero
  ¬¬Sp-hProp B = ¬hProp (¬Sp-hProp B)

  ¬¬Sp-isClosed : (B : Booleω) → isClosedProp (¬¬Sp-hProp B)
  ¬¬Sp-isClosed B = ¬-of-open-is-closed (¬Sp-hProp B) (¬Sp-isOpen B)

  -- tex Corollary 415: For Stone S, ¬¬S ↔ ||S||
  LemSurjectionsFormalToCompleteness-equiv : (B : Booleω)
    → ⟨ ¬¬Sp-hProp B ⟩ ≃ ∥ Sp B ∥₁
  LemSurjectionsFormalToCompleteness-equiv B =
    LemSurjectionsFormalToCompleteness.LemSurjectionsFormalToCompleteness-derived B

  truncSp-isClosed : (B : Booleω) → isClosedProp (∥ Sp B ∥₁ , squash₁)
  truncSp-isClosed B = transport (cong isClosedProp hProp-path) (¬¬Sp-isClosed B)
    where
    truncSp-Prop : hProp ℓ-zero
    truncSp-Prop = ∥ Sp B ∥₁ , squash₁

    equiv : ⟨ ¬¬Sp-hProp B ⟩ ≃ ⟨ truncSp-Prop ⟩
    equiv = LemSurjectionsFormalToCompleteness-equiv B

    fst-path : fst (¬¬Sp-hProp B) ≡ fst truncSp-Prop
    fst-path = ua equiv

    hProp-path : ¬¬Sp-hProp B ≡ truncSp-Prop
    hProp-path = Σ≡Prop {B = λ A → isProp A} (λ _ → isPropIsProp) fst-path

  TruncationStoneClosed : (S : Stone) → isClosedProp (∥ fst S ∥₁ , squash₁)
  TruncationStoneClosed (S , (B , p)) =
    transport (cong (λ X → isClosedProp (∥ X ∥₁ , squash₁)) p) (truncSp-isClosed B)

module Stone→closedPropModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open TruncationStoneClosedComplete

  Stone→closedProp : (P : hProp ℓ-zero) → hasStoneStr (fst P) → isClosedProp P
  Stone→closedProp P (B , p) = transport (cong isClosedProp hProp-path) truncClosed
    where
    SpB≡P : Sp B ≡ fst P
    SpB≡P = p

    truncSpClosed : isClosedProp (∥ Sp B ∥₁ , squash₁)
    truncSpClosed = truncSp-isClosed B

    propTruncIdem : ∥ fst P ∥₁ ≃ fst P
    propTruncIdem = propTruncIdempotent≃ (snd P)

    truncPath : ∥ Sp B ∥₁ ≡ fst P
    truncPath = cong ∥_∥₁ SpB≡P ∙ ua propTruncIdem

    truncProp : hProp ℓ-zero
    truncProp = ∥ Sp B ∥₁ , squash₁

    fst-path : fst truncProp ≡ fst P
    fst-path = truncPath

    truncClosed : isClosedProp truncProp
    truncClosed = truncSpClosed

    hProp-path : truncProp ≡ P
    hProp-path = Σ≡Prop {B = λ A → isProp A} (λ _ → isPropIsProp) fst-path

-- ClosedInStoneIsStone (tex Corollary 1770)
-- Proof sketch (from tex):
-- By StoneClosedSubsets (tex 1648), a subset A ⊆ S (for S : Stone) is closed iff
-- - Local choice (tex LocalChoiceSurjectionForm)
-- Detailed proof (from tex (ii) → (iii)):

module ClosedInStoneIsStoneModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)

  -- This is a consequence of StoneClosedSubsets (tex 1648).
  postulate
    ClosedInStoneIsStone : (S : Stone) → (A : fst S → hProp ℓ-zero)
                         → ((x : fst S) → isClosedProp (A x))
                         → hasStoneStr (Σ (fst S) (λ x → fst (A x)))

-- InhabitedClosedSubSpaceClosed (tex Corollary 1776)

module InhabitedClosedSubSpaceClosedModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open ClosedInStoneIsStoneModule
  open TruncationStoneClosedComplete

  InhabitedClosedSubSpaceClosed : (S : Stone) → (A : fst S → hProp ℓ-zero)
                                → ((x : fst S) → isClosedProp (A x))
                                → isClosedProp (∥ Σ (fst S) (λ x → fst (A x)) ∥₁ , squash₁)
  InhabitedClosedSubSpaceClosed S A A-closed =
    TruncationStoneClosed (Σ (fst S) (λ x → fst (A x)) , ClosedInStoneIsStone S A A-closed)

-- ClosedDependentSums / closedSigmaClosed (tex Corollary 1785)

module ClosedDependentSumsModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open ClosedPropIffStone
  open InhabitedClosedSubSpaceClosedModule

  closedSigmaClosed' : (P : hProp ℓ-zero) → isClosedProp P
                     → (Q : ⟨ P ⟩ → hProp ℓ-zero) → ((p : ⟨ P ⟩) → isClosedProp (Q p))
                     → isClosedProp (Σ ⟨ P ⟩ (λ p → fst (Q p)) , isOfHLevelΣ 1 (snd P) (λ p → snd (Q p)))
  closedSigmaClosed' P P-closed Q Q-closed = result
    where
    ΣPQ : Type₀
    ΣPQ = Σ ⟨ P ⟩ (λ p → fst (Q p))

    ΣPQ-isProp : isProp ΣPQ
    ΣPQ-isProp = isOfHLevelΣ 1 (snd P) (λ p → snd (Q p))

    ΣPQ-hProp : hProp ℓ-zero
    ΣPQ-hProp = ΣPQ , ΣPQ-isProp

    P-Stone : Stone
    P-Stone = fst P , closedProp→hasStoneStr P P-closed

    truncΣ-closed : isClosedProp (∥ ΣPQ ∥₁ , squash₁)
    truncΣ-closed = InhabitedClosedSubSpaceClosed P-Stone Q Q-closed

    propTruncIdem : ∥ ΣPQ ∥₁ ≃ ΣPQ
    propTruncIdem = propTruncIdempotent≃ ΣPQ-isProp

    fst-path : ∥ ΣPQ ∥₁ ≡ ΣPQ
    fst-path = ua propTruncIdem

    hProp-path : (∥ ΣPQ ∥₁ , squash₁) ≡ ΣPQ-hProp
    hProp-path = Σ≡Prop {B = λ A → isProp A} (λ _ → isPropIsProp) fst-path

    result : isClosedProp ΣPQ-hProp
    result = transport (cong isClosedProp hProp-path) truncΣ-closed

-- SDDecToElem: Stone Duality Correspondence (tex AxStoneDuality)

module SDDecToElemModule where
  open import Axioms.StoneDuality using (evaluationMap; StoneDualityAxiom; SDHomVersion)

  DecPredOnSp : (B : Booleω) → Type ℓ-zero
  DecPredOnSp B = Sp B → Bool

  elemFromDecPred : StoneDualityAxiom → (B : Booleω) → DecPredOnSp B → ⟨ fst B ⟩
  elemFromDecPred SD B D = invEq (fst (SDHomVersion SD B)) D

  elemFromDecPred-roundtrip : (SD : StoneDualityAxiom) (B : Booleω) (b : ⟨ fst B ⟩)
    → elemFromDecPred SD B (evaluationMap B b) ≡ b
  elemFromDecPred-roundtrip SD B b = retEq (fst (SDHomVersion SD B)) b

  decPredFromElem-roundtrip : (SD : StoneDualityAxiom) (B : Booleω) (D : DecPredOnSp B)
    → evaluationMap B (elemFromDecPred SD B D) ≡ D
  decPredFromElem-roundtrip SD B D = secEq (fst (SDHomVersion SD B)) D

  decPred-elem-correspondence : (SD : StoneDualityAxiom) (B : Booleω) (D : DecPredOnSp B)
    → let d = elemFromDecPred SD B D
      in (x : Sp B) → fst x d ≡ D x
  decPred-elem-correspondence SD B D x =
    cong (λ f → f x) (decPredFromElem-roundtrip SD B D)

-- closedSigmaClosed-derived (tex Corollary ClosedDependentSums 1785)

module ClosedSigmaClosedDerived where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open ClosedPropIffStone
  open InhabitedClosedSubSpaceClosedModule

  closedSigmaClosed-derived : (P : hProp ℓ-zero) → isClosedProp P
                            → (Q : ⟨ P ⟩ → hProp ℓ-zero) → ((p : ⟨ P ⟩) → isClosedProp (Q p))
                            → isClosedProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
  closedSigmaClosed-derived P P-closed Q Q-closed =
    InhabitedClosedSubSpaceClosed P-Stone Q Q-closed
    where
    P-Stone : Stone
    P-Stone = fst P , closedProp→hasStoneStr P P-closed

-- StoneEqualityClosed (tex Lemma 1636)
-- Proof (from tex):
