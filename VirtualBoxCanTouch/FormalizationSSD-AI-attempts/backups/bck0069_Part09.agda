{-# OPTIONS --cubical --guardedness #-}

module work.Part09 where

open import work.Part08 public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv using (_≃_; fiber; isEquiv)
open isEquiv
open import Cubical.Foundations.Powerset using (_∈_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; squash₁)
open import Cubical.Algebra.BooleanRing using (BooleanRing; BooleanRingStr; BoolHom; BooleanRing→CommRing)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; has-Boole-ω')
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.Foundations.Isomorphism using (Iso; iso; invIso; isoToPath)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr; CommRing→Ring)
open import Cubical.Algebra.Ring.Properties using (module RingTheory)

-- ClosedInStoneIsStone (tex Corollary 1770)
module ClosedInStoneIsStoneModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isPropHasStoneStr; isSetBoolHom)
  open import Cubical.Foundations.HLevels using (isSetΣ; isPropΠ)
  open import Cubical.Foundations.Transport using (transportTransport⁻; transport⁻Transport)
  open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
  open import Cubical.Foundations.Equiv using (compEquiv)
  open import Cubical.Foundations.Univalence using (ua)
  open SDDecToElemModule
  open StoneClosedSubsetsModule

  ClosedInStoneIsStone : (S : Stone) → (A : fst S → hProp ℓ-zero)
                       → ((x : fst S) → isClosedProp (A x))
                       → hasStoneStr (Σ (fst S) (λ x → fst (A x)))
  ClosedInStoneIsStone S A A-closed =
    PT.rec (isPropHasStoneStr sd-axiom _) construct (snd (fst (snd S)))
    where
    |S| : Type ℓ-zero
    |S| = fst S

    S-isSet : isSet |S|
    S-isSet = subst isSet (snd (snd S)) (isSetBoolHom (fst (fst (snd S))) BoolBR)

    ΣA-isSet : isSet (Σ |S| (λ x → fst (A x)))
    ΣA-isSet = isSetΣ S-isSet (λ x → isProp→isSet (snd (A x)))

    α : |S| → ℕ → Bool
    α x = fst (A-closed x)

    A→allFalse : (x : |S|) → fst (A x) → (n : ℕ) → α x n ≡ false
    A→allFalse x = fst (snd (A-closed x))

    allFalse→A : (x : |S|) → ((n : ℕ) → α x n ≡ false) → fst (A x)
    allFalse→A x = snd (snd (A-closed x))

    construct : has-Boole-ω' (fst (fst (snd S))) → hasStoneStr (Σ |S| (λ x → fst (A x)))
    construct (f₀ , equiv₀) = PT.rec propHasStoneStrΣA extractC (quotientBySeqPreservesBooleω B d)
      where
      propHasStoneStrΣA : isProp (hasStoneStr (Σ |S| (λ x → fst (A x))))
      propHasStoneStrΣA = isPropHasStoneStr sd-axiom (Σ |S| (λ x → fst (A x)))

      B : Booleω
      B = fst (snd S)

      SpB≡S : Sp B ≡ |S|
      SpB≡S = snd (snd S)

      α' : Sp B → ℕ → Bool
      α' x n = α (transport SpB≡S x) n

      D : ℕ → Sp B → Bool
      D n x = α' x n

      d : ℕ → ⟨ fst B ⟩
      d n = elemFromDecPred sd-axiom B (D n)

      d-property : (n : ℕ) (x : Sp B) → fst x (d n) ≡ α' x n
      d-property n x = decPred-elem-correspondence sd-axiom B (D n) x

      extractC : Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)))
               → hasStoneStr (Σ |S| (λ x → fst (A x)))
      extractC (C , SpC≃ClosedSubset) = C , SpC≡ΣA
        where
        ClosedSubsetB : Type ℓ-zero
        ClosedSubsetB = Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)

        ClosedSubsetB→ΣA : ClosedSubsetB → Σ |S| (λ y → fst (A y))
        ClosedSubsetB→ΣA (x , all-zero) = transport SpB≡S x , allFalse→A (transport SpB≡S x) allFalse'
          where
          allFalse' : (n : ℕ) → α (transport SpB≡S x) n ≡ false
          allFalse' n =
            α (transport SpB≡S x) n   ≡⟨ sym (d-property n x) ⟩
            fst x (d n)               ≡⟨ all-zero n ⟩
            false ∎

        ΣA→ClosedSubsetB : Σ |S| (λ y → fst (A y)) → ClosedSubsetB
        ΣA→ClosedSubsetB (y , Ay) = x , all-zero
          where
          x : Sp B
          x = transport (sym SpB≡S) y

          all-zero : (n : ℕ) → fst x (d n) ≡ false
          all-zero n =
            fst x (d n)             ≡⟨ d-property n x ⟩
            α (transport SpB≡S x) n ≡⟨ cong (λ z → α z n) (transportTransport⁻ SpB≡S y) ⟩
            α y n                   ≡⟨ A→allFalse y Ay n ⟩
            false ∎

        ClosedSubsetB→ΣA→ClosedSubsetB : (xa : ClosedSubsetB) → ΣA→ClosedSubsetB (ClosedSubsetB→ΣA xa) ≡ xa
        ClosedSubsetB→ΣA→ClosedSubsetB (x , all-zero) =
          Σ≡Prop (λ _ → isPropΠ (λ _ → isSetBool _ _))
                 (transport⁻Transport SpB≡S x)

        ΣA→ClosedSubsetB→ΣA : (yAy : Σ |S| (λ y → fst (A y))) → ClosedSubsetB→ΣA (ΣA→ClosedSubsetB yAy) ≡ yAy
        ΣA→ClosedSubsetB→ΣA (y , Ay) =
          Σ≡Prop (λ z → snd (A z))
                 (transportTransport⁻ SpB≡S y)

        ClosedSubsetB≃ΣA : ClosedSubsetB ≃ Σ |S| (λ y → fst (A y))
        ClosedSubsetB≃ΣA = isoToEquiv (iso ClosedSubsetB→ΣA ΣA→ClosedSubsetB ΣA→ClosedSubsetB→ΣA ClosedSubsetB→ΣA→ClosedSubsetB)

        SpC≃ΣA : Sp C ≃ Σ |S| (λ y → fst (A y))
        SpC≃ΣA = compEquiv SpC≃ClosedSubset ClosedSubsetB≃ΣA

        SpC≡ΣA : Sp C ≡ Σ |S| (λ y → fst (A y))
        SpC≡ΣA = ua SpC≃ΣA

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

module StoneSeparatedModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isSetBoolHom)
  open StoneClosedSubsetsModule
  open SDDecToElemModule

  ClosedSubsetOfStone : Stone → Type₁
  ClosedSubsetOfStone S = Σ[ A ∈ (fst S → hProp ℓ-zero) ] ((x : fst S) → isClosedProp (A x))

  DecSubsetOfStone : Stone → Type₀
  DecSubsetOfStone S = fst S → Bool

  ClosedSubsetsDisjoint : (S : Stone) → ClosedSubsetOfStone S → ClosedSubsetOfStone S → Type₀
  ClosedSubsetsDisjoint S (F , _) (G , _) = (x : fst S) → fst (F x) → fst (G x) → ⊥

  ClosedSubDec : (S : Stone) → ClosedSubsetOfStone S → DecSubsetOfStone S → Type₀
  ClosedSubDec S (A , _) D = (x : fst S) → fst (A x) → D x ≡ true

  ClosedSubNotDec : (S : Stone) → ClosedSubsetOfStone S → DecSubsetOfStone S → Type₀
  ClosedSubNotDec S (A , _) D = (x : fst S) → fst (A x) → D x ≡ false

  -- tex Lemma 1824
  postulate
    StoneSeparated : (S : Stone)
      → (F G : ClosedSubsetOfStone S)
      → ClosedSubsetsDisjoint S F G
      → ∥ Σ[ D ∈ DecSubsetOfStone S ] (ClosedSubDec S F D) × (ClosedSubNotDec S G D) ∥₁

-- StoneAsClosedSubsetOfCantor (tex Lemma 2082)
module CantorIsStoneModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; SpGeneralBooleanRing)
  open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; freeBA-universal-property; generator)
  import QuotientBool as QB
  open import CommRingQuotients.IdealTerms using (isInIdeal; isImage; iszero; isSum; isMul; idealDecomp)
  open import CommRingQuotients.TrivialIdeal using (quotientFiber)
  import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
  open import Cubical.Algebra.CommRing.Quotient.Base using (quotientHomSurjective)
  open import Cubical.HITs.PropositionalTruncation as PT
  open import Cubical.Data.Sigma using (Σ≡Prop)
  open import Cubical.Functions.Surjection
  open import Cubical.Tactics.CommRingSolver

  private
    R = BooleanRing→CommRing (freeBA ℕ)
  open BooleanRingStr (snd (freeBA ℕ)) using (𝟘; 𝟙)

  constZero : ℕ → ⟨ freeBA ℕ ⟩
  constZero _ = BooleanRingStr.𝟘 (snd (freeBA ℕ))

  private
    R' = R IQ./Im constZero
    I' = IQ.genIdeal R constZero
    instance
      _ = snd R'

    π = IQ.quotientImageHom R constZero

    is-set' : isSet ⟨ R' ⟩
    is-set' = CommRingStr.is-set (snd R')

    private
      module CRS = CommRingStr (snd R)
    _+R_ = CRS._+_
    _·R_ = CRS._·_
    _-R_ = CRS._-_
    0R = CRS.0r

    trivConstZero : (i : ⟨ R ⟩) → isInIdeal R constZero i → i ≡ 0R
    trivConstZero i (isImage .i n p) = sym p
    trivConstZero i (iszero .i p) = sym p
    trivConstZero i (isSum .i s t i=s+t s∈I t∈I) =
      i           ≡⟨ i=s+t ⟩
      s +R t      ≡⟨ cong₂ _+R_ (trivConstZero s s∈I) (trivConstZero t t∈I) ⟩
      0R +R 0R    ≡⟨ CRS.+IdL 0R ⟩
      0R          ∎
    trivConstZero i (isMul .i s t i=st t∈I) =
      i           ≡⟨ i=st ⟩
      s ·R t      ≡⟨ cong (s ·R_) (trivConstZero t t∈I) ⟩
      s ·R 0R     ≡⟨ RingTheory.0RightAnnihilates (CommRing→Ring R) s ⟩
      0R          ∎

    fiberProp : (c : ⟨ R' ⟩) → isProp (fiber (fst π) c)
    fiberProp c (x , qx=c) (y , qy=c) = Σ≡Prop (λ d → is-set' _ _) help'' where
      help : (x -R y) ∈ fst I'
      help = quotientFiber R I' x y (qx=c ∙ sym qy=c)

      help' : x -R y ≡ 0R
      help' = PT.rec (CRS.is-set _ _) (trivConstZero (x -R y)) (idealDecomp R constZero (x -R y) help)

      help'' : x ≡ y
      help'' = x ≡⟨ solve! R ⟩ (x -R y) +R y ≡⟨ cong (_+R y) help' ⟩ 0R +R y ≡⟨ solve! R ⟩ y ∎

    fiberInhabited : (c : ⟨ R' ⟩) → fiber (fst π) c
    fiberInhabited c = transport (propTruncIdempotent (fiberProp c))
      (quotientHomSurjective R I' c)

  opaque
    unfolding QB._/Im_
    quotientByConstZero≃Original : BooleanRingEquiv (freeBA ℕ) (freeBA ℕ QB./Im constZero)
    fst (fst quotientByConstZero≃Original) = fst π
    equiv-proof (snd (fst quotientByConstZero≃Original)) y = fiberInhabited y , fiberProp y _
    snd quotientByConstZero≃Original = snd π

  freeBA-ℕ-is-Booleω' : has-Boole-ω' (freeBA ℕ)
  freeBA-ℕ-is-Booleω' = constZero , quotientByConstZero≃Original

  freeBA-ℕ-Booleω : Booleω
  freeBA-ℕ-Booleω = freeBA ℕ , ∣ freeBA-ℕ-is-Booleω' ∣₁

  Sp-freeBA-ℕ-Iso : Iso (SpGeneralBooleanRing (freeBA ℕ)) CantorSpace
  Sp-freeBA-ℕ-Iso = invIso (freeBA-universal-property ℕ BoolBR)

  Sp-freeBA-ℕ-≡-Cantor : SpGeneralBooleanRing (freeBA ℕ) ≡ CantorSpace
  Sp-freeBA-ℕ-≡-Cantor = isoToPath Sp-freeBA-ℕ-Iso

  CantorIsStone : hasStoneStr CantorSpace
  CantorIsStone = freeBA-ℕ-Booleω , Sp-freeBA-ℕ-≡-Cantor
