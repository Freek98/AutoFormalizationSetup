{-# OPTIONS --cubical --guardedness #-}

open import work.Part02Defs using (FoundationalAxioms)

module work.Part09 (fa : FoundationalAxioms) where

open import work.Part08 fa public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv using (_≃_; fiber; isEquiv)
open isEquiv
open import Cubical.Foundations.Powerset using (_∈_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.Nat using (ℕ; suc; zero; max) renaming (_+_ to _+ℕ_; _∸_ to _∸ℕ_)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; squash₁)
open import Cubical.Algebra.BooleanRing using (BooleanRing; BooleanRingStr; BoolHom; BooleanRing→CommRing; module BooleanAlgebraStr)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; has-Boole-ω')
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.Foundations.Isomorphism using (Iso; iso; invIso; isoToPath)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr; CommRing→Ring)
open import Cubical.Algebra.Ring.Properties using (module RingTheory)

-- ClosedInStoneIsStone (tex Corollary 1770)
module ClosedInStoneIsStoneModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isPropHasStoneStr; isSetBoolHom)
  open import Cubical.Foundations.HLevels using (isPropΠ)
  open import Cubical.Foundations.Transport using (transportTransport⁻; transport⁻Transport)
  open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
  open import Cubical.Foundations.Equiv using (compEquiv)
  open import Cubical.Foundations.Univalence using (ua)
  open SDDecToElemModule
  open StoneClosedSubsetsModule

  open ODiscAxioms
  open import Cubical.Foundations.Equiv using (equivFun; invEq; secEq)

  -- tex Theorem StoneClosedSubsets, (v)→(i) direction
  -- Proved from localChoice-axiom + ImageStoneMapDecidableIntersection + quotientBySeqPreservesBooleω
  closedFamilyChoice : (S : Stone) (A : fst S → hProp ℓ-zero)
    → ((x : fst S) → isClosedProp (A x))
    → ∥ ((x : fst S) → Σ[ α ∈ binarySequence ] ⟨ A x ⟩ ↔ ((n : ℕ) → α n ≡ false)) ∥₁
  closedFamilyChoice S A A-closed =
    PT.rec squash₁ step1 (localChoice-axiom B P P-trunc)
    where
    |S| = fst S
    B : Booleω
    B = fst (snd S)
    SpB≡S : Sp B ≡ |S|
    SpB≡S = snd (snd S)
    P : Sp B → Type ℓ-zero
    P s = Σ[ α ∈ binarySequence ] ⟨ A (transport SpB≡S s) ⟩ ↔ ((n : ℕ) → α n ≡ false)
    P-trunc : (s : Sp B) → ∥ P s ∥₁
    P-trunc s = A-closed (transport SpB≡S s)

    step1 : Σ[ C ∈ Booleω ] Σ[ q ∈ (Sp C → Sp B) ]
              (isSurjectiveSpMap {B} {C} q × ((t : Sp C) → P (q t)))
          → ∥ ((x : |S|) → Σ[ α ∈ binarySequence ] ⟨ A x ⟩ ↔ ((n : ℕ) → α n ≡ false)) ∥₁
    step1 (C , q , q-surj , h) =
      PT.rec squash₁ step2 (quotientBySeqPreservesBooleω C d')
      where
      β : Sp C → ℕ → Bool
      β c n = fst (h c) n
      d' : ℕ → ⟨ fst C ⟩
      d' n = elemFromDecPred sd-axiom C (λ c → β c n)
      d'-prop : (n : ℕ) (c : Sp C) → fst c (d' n) ≡ β c n
      d'-prop n c = decPred-elem-correspondence sd-axiom C (λ c → β c n) c

      step2 : Σ[ T ∈ Booleω ] (Sp T ≃ (Σ[ c ∈ Sp C ] ((n : ℕ) → fst c (d' n) ≡ false)))
            → ∥ ((x : |S|) → Σ[ α ∈ binarySequence ] ⟨ A x ⟩ ↔ ((n : ℕ) → α n ≡ false)) ∥₁
      step2 (T , SpT≃CS) =
        PT.rec squash₁ step3 (ImageStoneMapDecidableIntersection B T fT→B)
        where
        fT→B : Sp T → Sp B
        fT→B t = q (fst (equivFun SpT≃CS t))

        -- Im(fT→B)(x) ↔ A(transport SpB≡S x)
        imf→A : (x : Sp B) → ∥ Σ[ t ∈ Sp T ] fT→B t ≡ x ∥₁ → ⟨ A (transport SpB≡S x) ⟩
        imf→A x = PT.rec (snd (A (transport SpB≡S x))) go
          where
          go : Σ[ t ∈ Sp T ] fT→B t ≡ x → ⟨ A (transport SpB≡S x) ⟩
          go (t , ft≡x) = subst (λ z → ⟨ A (transport SpB≡S z) ⟩) ft≡x witness
            where
            cs = equivFun SpT≃CS t
            c = fst cs
            c-all-false : (n : ℕ) → fst c (d' n) ≡ false
            c-all-false = snd cs
            β-false : (n : ℕ) → β c n ≡ false
            β-false n = sym (d'-prop n c) ∙ c-all-false n
            witness : ⟨ A (transport SpB≡S (q c)) ⟩
            witness = snd (snd (h c)) β-false

        A→imf : (x : Sp B) → ⟨ A (transport SpB≡S x) ⟩ → ∥ Σ[ t ∈ Sp T ] fT→B t ≡ x ∥₁
        A→imf x Ax = PT.rec squash₁ go (q-surj x)
          where
          go : Σ[ c ∈ Sp C ] q c ≡ x → ∥ Σ[ t ∈ Sp T ] fT→B t ≡ x ∥₁
          go (c , qc≡x) = ∣ t , ft≡x ∣₁
            where
            Aqc : ⟨ A (transport SpB≡S (q c)) ⟩
            Aqc = subst (λ z → ⟨ A (transport SpB≡S z) ⟩) (sym qc≡x) Ax
            β-false : (n : ℕ) → β c n ≡ false
            β-false = fst (snd (h c)) Aqc
            c-all-false : (n : ℕ) → fst c (d' n) ≡ false
            c-all-false n = d'-prop n c ∙ β-false n
            cs : Σ[ c' ∈ Sp C ] ((n : ℕ) → fst c' (d' n) ≡ false)
            cs = c , c-all-false
            t : Sp T
            t = invEq SpT≃CS cs
            ft≡x : fT→B t ≡ x
            ft≡x =
              q (fst (equivFun SpT≃CS (invEq SpT≃CS cs))) ≡⟨ cong (λ z → q (fst z)) (secEq SpT≃CS cs) ⟩
              q c                                           ≡⟨ qc≡x ⟩
              x ∎

        step3 : Σ[ d ∈ (ℕ → ⟨ fst B ⟩) ]
                  ((x : Sp B) → (∥ Σ[ t ∈ Sp T ] fT→B t ≡ x ∥₁) ↔ ((n : ℕ) → fst x (d n) ≡ false))
              → ∥ ((y : |S|) → Σ[ α ∈ binarySequence ] ⟨ A y ⟩ ↔ ((n : ℕ) → α n ≡ false)) ∥₁
        step3 (d , d-iff) = ∣ result ∣₁
          where
          result : (y : |S|) → Σ[ α ∈ binarySequence ] ⟨ A y ⟩ ↔ ((n : ℕ) → α n ≡ false)
          result y = α-y , fwd , bwd
            where
            x : Sp B
            x = transport (sym SpB≡S) y
            α-y : binarySequence
            α-y n = fst x (d n)
            fwd : ⟨ A y ⟩ → (n : ℕ) → α-y n ≡ false
            fwd Ay = fst (d-iff x) (A→imf x (subst (λ z → ⟨ A z ⟩) (sym (transportTransport⁻ SpB≡S y)) Ay))
            bwd : ((n : ℕ) → α-y n ≡ false) → ⟨ A y ⟩
            bwd all-false = subst (λ z → ⟨ A z ⟩) (transportTransport⁻ SpB≡S y)
              (imf→A x (snd (d-iff x) all-false))

  ClosedInStoneIsStone : (S : Stone) → (A : fst S → hProp ℓ-zero)
                       → ((x : fst S) → isClosedProp (A x))
                       → hasStoneStr (Σ (fst S) (λ x → fst (A x)))
  ClosedInStoneIsStone S A A-closed =
    PT.rec (isPropHasStoneStr sd-axiom _) mainConstruct (closedFamilyChoice S A A-closed)
    where
    |S| : Type ℓ-zero
    |S| = fst S

    mainConstruct : ((x : |S|) → Σ[ α ∈ binarySequence ] ⟨ A x ⟩ ↔ ((n : ℕ) → α n ≡ false))
                  → hasStoneStr (Σ |S| (λ x → fst (A x)))
    mainConstruct A-closed-bare =
      PT.rec (isPropHasStoneStr sd-axiom _) extractC (quotientBySeqPreservesBooleω B d)
      where
      α : |S| → ℕ → Bool
      α x = fst (A-closed-bare x)

      B : Booleω
      B = fst (snd S)

      SpB≡S : Sp B ≡ |S|
      SpB≡S = snd (snd S)

      α' : Sp B → ℕ → Bool
      α' x n = α (transport SpB≡S x) n

      d : ℕ → ⟨ fst B ⟩
      d n = elemFromDecPred sd-axiom B (λ x → α' x n)

      d-property : (n : ℕ) (x : Sp B) → fst x (d n) ≡ α' x n
      d-property n x = decPred-elem-correspondence sd-axiom B (λ x → α' x n) x

      extractC : Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)))
               → hasStoneStr (Σ |S| (λ x → fst (A x)))
      extractC (C , SpC≃ClosedSubset) = C , SpC≡ΣA
        where
        ClosedSubsetB : Type ℓ-zero
        ClosedSubsetB = Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)

        ClosedSubsetB→ΣA : ClosedSubsetB → Σ |S| (λ y → fst (A y))
        ClosedSubsetB→ΣA (x , all-zero) = transport SpB≡S x , snd (snd (A-closed-bare (transport SpB≡S x))) (λ n →
            α (transport SpB≡S x) n   ≡⟨ sym (d-property n x) ⟩
            fst x (d n)               ≡⟨ all-zero n ⟩
            false ∎)

        ΣA→ClosedSubsetB : Σ |S| (λ y → fst (A y)) → ClosedSubsetB
        ΣA→ClosedSubsetB (y , Ay) = x , all-zero
          where
          x : Sp B
          x = transport (sym SpB≡S) y

          all-zero : (n : ℕ) → fst x (d n) ≡ false
          all-zero n =
            fst x (d n)             ≡⟨ d-property n x ⟩
            α (transport SpB≡S x) n ≡⟨ cong (λ z → α z n) (transportTransport⁻ SpB≡S y) ⟩
            α y n                   ≡⟨ fst (snd (A-closed-bare y)) Ay n ⟩
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

open ClosedSigmaClosedDerived

-- isClosedSubset (tex Definition 884-886, closed analog)
isClosedSubset : {T : Type₀} → (A : T → hProp ℓ-zero) → Type₀
isClosedSubset {T} A = (t : T) → isClosedProp (A t)

-- Preimage of closed subset is closed (tex remark 889 analog)
preimageClosedIsClosed : {S T : Type₀} (f : S → T) (A : T → hProp ℓ-zero)
                       → isClosedSubset A → isClosedSubset (λ s → A (f s))
preimageClosedIsClosed f A Aclosed s = Aclosed (f s)

-- Transitivity of closedness (tex Remark ClosedTransitive 1794)
closedSubsetTransitive : {T : Type₀}
  → (V : T → hProp ℓ-zero) → isClosedSubset V
  → (W : (t : T) → ⟨ V t ⟩ → hProp ℓ-zero)
  → ((t : T) (v : ⟨ V t ⟩) → isClosedProp (W t v))
  → isClosedSubset (λ t → (∥ Σ[ v ∈ ⟨ V t ⟩ ] ⟨ W t v ⟩ ∥₁) , squash₁)
closedSubsetTransitive V Vclosed W Wclosed t =
  closedSigmaClosed-derived (V t) (Vclosed t) (W t) (Wclosed t)

-- Opaque bridge: 0≡1 in BooleanRing quotient → 1 in CommRing ideal
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import CommRingQuotients.IdealTerms using (isInIdeal; isImage; iszero; isSum; isMul; idealDecomp)
open import CommRingQuotients.TrivialIdeal using (trivialQuotient→1∈I)
import QuotientBool as QB

opaque
  unfolding QB._/Im_
  0≡1-quotient→1∈ideal : (B : BooleanRing ℓ-zero) (d : ℕ → ⟨ B ⟩)
    → BooleanRingStr.𝟘 (snd (B QB./Im d)) ≡ BooleanRingStr.𝟙 (snd (B QB./Im d))
    → IQ.generatedIdeal (BooleanRing→CommRing B) d
        (CommRingStr.1r (snd (BooleanRing→CommRing B)))
  0≡1-quotient→1∈ideal B d p =
    trivialQuotient→1∈I (BooleanRing→CommRing B) (IQ.genIdeal (BooleanRing→CommRing B) d) (sym p)

-- Finite join in a Boolean ring (defined using ring ops directly)
finJoinBR : (B : BooleanRing ℓ-zero) → (ℕ → ⟨ B ⟩) → ℕ → ⟨ B ⟩
finJoinBR B d zero = BooleanRingStr.𝟘 (snd B)
finJoinBR B d (suc n) = BooleanAlgebraStr._∨_ B (d n) (finJoinBR B d n)

-- General ideal bound: from 0≡1 in B/d, extract N with finJoinBR d N ≡ 1
module IdealBound (B : BooleanRing ℓ-zero) (d : ℕ → ⟨ B ⟩) where
  private
    R = BooleanRing→CommRing B
    module CRS = CommRingStr (snd R)
    module BA = BooleanAlgebraStr B
    𝟘B = BooleanRingStr.𝟘 (snd B)
    _∨B_ = BA._∨_
    _·B_ = CRS._·_
    _+B_ = CRS._+_
    fJ = finJoinBR B d

  leq-suc : {r : ⟨ B ⟩} (N : ℕ) → r ·B fJ N ≡ r → r ·B fJ (suc N) ≡ r
  leq-suc {r} N p =
    r ·B (d N ∨B fJ N)
      ≡⟨ sym (cong (_·B (d N ∨B fJ N)) p) ⟩
    (r ·B fJ N) ·B (d N ∨B fJ N)
      ≡⟨ sym (CRS.·Assoc r (fJ N) (d N ∨B fJ N)) ⟩
    r ·B (fJ N ·B (d N ∨B fJ N))
      ≡⟨ cong (r ·B_) (cong (fJ N ·B_) BA.∨Comm) ⟩
    r ·B (fJ N ·B (fJ N ∨B d N))
      ≡⟨ cong (r ·B_) BA.∧AbsorbL∨ ⟩
    r ·B fJ N
      ≡⟨ p ⟩
    r ∎

  leq-extend : {r : ⟨ B ⟩} (N k : ℕ) → r ·B fJ N ≡ r → r ·B fJ (k +ℕ N) ≡ r
  leq-extend N zero p = p
  leq-extend N (suc k) p = leq-suc (k +ℕ N) (leq-extend N k p)

  leq-max-left : {r : ⟨ B ⟩} (N₁ N₂ : ℕ) → r ·B fJ N₁ ≡ r → r ·B fJ (max N₁ N₂) ≡ r
  leq-max-left {r} N₁ N₂ p =
    subst (λ M → r ·B fJ M ≡ r) (≤-∸-+-cancel {N₁} {max N₁ N₂} (left-≤-max {N₁} {N₂}))
          (leq-extend N₁ (max N₁ N₂ ∸ℕ N₁) p)
    where open import Cubical.Data.Nat.Order using (left-≤-max; ≤-∸-+-cancel)

  leq-max-right : {r : ⟨ B ⟩} (N₁ N₂ : ℕ) → r ·B fJ N₂ ≡ r → r ·B fJ (max N₁ N₂) ≡ r
  leq-max-right {r} N₁ N₂ p =
    subst (λ M → r ·B fJ M ≡ r) (≤-∸-+-cancel {N₂} {max N₁ N₂} (right-≤-max {N₂} {N₁}))
          (leq-extend N₂ (max N₁ N₂ ∸ℕ N₂) p)
    where open import Cubical.Data.Nat.Order using (right-≤-max; ≤-∸-+-cancel)

  idealBound : {r : ⟨ B ⟩} → isInIdeal R d r → Σ[ N ∈ ℕ ] (r ·B fJ N ≡ r)
  idealBound (isImage r n p) = suc n ,
    (r ·B (d n ∨B fJ n)
      ≡⟨ cong (λ z → z ·B (d n ∨B fJ n)) (sym p) ⟩
    d n ·B (d n ∨B fJ n)
      ≡⟨ BA.∧AbsorbL∨ ⟩
    d n
      ≡⟨ p ⟩
    r ∎)
  idealBound (iszero r p) = zero ,
    (r ·B 𝟘B
      ≡⟨ cong (λ z → z ·B 𝟘B) (sym p) ⟩
    𝟘B ·B 𝟘B
      ≡⟨ RingTheory.0LeftAnnihilates (CommRing→Ring R) 𝟘B ⟩
    𝟘B
      ≡⟨ p ⟩
    r ∎)
  idealBound (isSum r s t r=s+t sI tI) =
    let (N₁ , p₁) = idealBound sI
        (N₂ , p₂) = idealBound tI
        M = max N₁ N₂
        p₁' = leq-max-left {s} N₁ N₂ p₁
        p₂' = leq-max-right {t} N₁ N₂ p₂
    in M ,
      (r ·B fJ M
        ≡⟨ cong (_·B fJ M) r=s+t ⟩
      (s +B t) ·B fJ M
        ≡⟨ CRS.·Comm (s +B t) (fJ M) ⟩
      fJ M ·B (s +B t)
        ≡⟨ CRS.·DistR+ (fJ M) s t ⟩
      (fJ M ·B s) +B (fJ M ·B t)
        ≡⟨ cong₂ _+B_ (CRS.·Comm (fJ M) s) (CRS.·Comm (fJ M) t) ⟩
      (s ·B fJ M) +B (t ·B fJ M)
        ≡⟨ cong₂ _+B_ p₁' p₂' ⟩
      s +B t
        ≡⟨ sym r=s+t ⟩
      r ∎)
  idealBound (isMul r s t r=st tI) =
    let (N , p) = idealBound tI
    in N ,
      (r ·B fJ N
        ≡⟨ cong (_·B fJ N) r=st ⟩
      (s ·B t) ·B fJ N
        ≡⟨ sym (CRS.·Assoc s t (fJ N)) ⟩
      s ·B (t ·B fJ N)
        ≡⟨ cong (s ·B_) p ⟩
      s ·B t
        ≡⟨ sym r=st ⟩
      r ∎)

  -- Combined: 0≡1 in B/d → ∃ N. finJoinBR d N ≡ 1
  extract-finJoin-bound : BooleanRingStr.𝟘 (snd (B QB./Im d)) ≡ BooleanRingStr.𝟙 (snd (B QB./Im d))
    → ∥ Σ[ N ∈ ℕ ] finJoinBR B d N ≡ BooleanRingStr.𝟙 (snd B) ∥₁
  extract-finJoin-bound 0≡1 = PT.map go (idealDecomp R d _ (0≡1-quotient→1∈ideal B d 0≡1))
    where
    go : isInIdeal R d (CRS.1r) → Σ[ N ∈ ℕ ] fJ N ≡ BooleanRingStr.𝟙 (snd B)
    go iI = let (N , p) = idealBound iI in N , sym (CRS.·IdL (fJ N)) ∙ p

-- tex Lemma 1824 (StoneSeperated)
module StoneSeparatedModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isSetBoolHom)
  open StoneClosedSubsetsModule
  open SDDecToElemModule
  open ClosedInStoneIsStoneModule using (closedFamilyChoice)
  open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
  import Cubical.Data.Sum as ⊎
  open import Cubical.Foundations.Transport using (transport⁻Transport; transportTransport⁻)
  open import Cubical.Foundations.HLevels using (isPropΠ)
  open import Cubical.Foundations.Equiv using (equivFun; invEq)
  open import Cubical.Algebra.CommRing using (_$cr_; IsCommRingHom)
  open import Cubical.Data.Nat using (_+_; max)
  open import Cubical.Data.Nat.Order using (_≤_; _<_)

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
  StoneSeparated : (S : Stone)
    → (F G : ClosedSubsetOfStone S)
    → ClosedSubsetsDisjoint S F G
    → ∥ Σ[ D ∈ DecSubsetOfStone S ] (ClosedSubDec S F D) × (ClosedSubNotDec S G D) ∥₁
  StoneSeparated S (F , F-closed) (G , G-closed) disjoint =
    PT.rec2 squash₁ mainProof
      (closedFamilyChoice S F F-closed)
      (closedFamilyChoice S G G-closed)
    where
    |S| = fst S
    B : Booleω
    B = fst (snd S)
    SpB≡S = snd (snd S)

    mainProof : ((x : |S|) → Σ[ α ∈ binarySequence ] fst (F x) ↔ ((n : ℕ) → α n ≡ false))
              → ((x : |S|) → Σ[ α ∈ binarySequence ] fst (G x) ↔ ((n : ℕ) → α n ≡ false))
              → ∥ Σ[ D ∈ DecSubsetOfStone S ] (ClosedSubDec S (F , F-closed) D) × (ClosedSubNotDec S (G , G-closed) D) ∥₁
    mainProof F-wit G-wit = PT.rec squash₁ fromIdeal idealMem
      where
      private
        module BA = BooleanAlgebraStr (fst B)

      f-pred : ℕ → Sp B → Bool
      f-pred n x = fst (F-wit (transport SpB≡S x)) n

      g-pred : ℕ → Sp B → Bool
      g-pred n x = fst (G-wit (transport SpB≡S x)) n

      f-elem : ℕ → ⟨ fst B ⟩
      f-elem n = elemFromDecPred sd-axiom B (f-pred n)

      g-elem : ℕ → ⟨ fst B ⟩
      g-elem n = elemFromDecPred sd-axiom B (g-pred n)

      f-prop : (n : ℕ) (x : Sp B) → fst x (f-elem n) ≡ f-pred n x
      f-prop n x = decPred-elem-correspondence sd-axiom B (f-pred n) x

      g-prop : (n : ℕ) (x : Sp B) → fst x (g-elem n) ≡ g-pred n x
      g-prop n x = decPred-elem-correspondence sd-axiom B (g-pred n) x

      encode : ℕ ⊎.⊎ ℕ → ℕ
      encode = Iso.fun ℕ⊎ℕ≅ℕ

      decode : ℕ → ℕ ⊎.⊎ ℕ
      decode = Iso.inv ℕ⊎ℕ≅ℕ

      d : ℕ → ⟨ fst B ⟩
      d n = ⊎.rec f-elem g-elem (decode n)

      d-at-f : (m : ℕ) → d (encode (⊎.inl m)) ≡ f-elem m
      d-at-f m = cong (⊎.rec f-elem g-elem) (Iso.ret ℕ⊎ℕ≅ℕ (⊎.inl m))

      d-at-g : (m : ℕ) → d (encode (⊎.inr m)) ≡ g-elem m
      d-at-g m = cong (⊎.rec f-elem g-elem) (Iso.ret ℕ⊎ℕ≅ℕ (⊎.inr m))

      -- The quotient B/d as a Booleω
      B/d-Booleω : Booleω
      B/d-Booleω = fst B QB./Im d , quotientBySeqHasBooleω B d

      -- Sp(B/d) ≃ ClosedSubset via SpOfQuotientBySeq
      open SpOfQuotientBySeq (fst B) d using (Sp-quotient-≃; Sp-quotient→ClosedSubset)

      -- The closed subset for d is F∩G, which is empty
      spEmpty : Sp B/d-Booleω → ⊥
      spEmpty sp-hom =
        let (x , allZero) = equivFun Sp-quotient-≃ sp-hom
            y : |S|
            y = transport SpB≡S x
            -- x sends all f-elem to false → y ∈ F
            f-false : (n : ℕ) → fst x (f-elem n) ≡ false
            f-false n =
              fst x (f-elem n)
                ≡⟨ cong (fst x) (sym (d-at-f n)) ⟩
              fst x (d (encode (⊎.inl n)))
                ≡⟨ allZero (encode (⊎.inl n)) ⟩
              false ∎
            g-false : (n : ℕ) → fst x (g-elem n) ≡ false
            g-false n =
              fst x (g-elem n)
                ≡⟨ cong (fst x) (sym (d-at-g n)) ⟩
              fst x (d (encode (⊎.inr n)))
                ≡⟨ allZero (encode (⊎.inr n)) ⟩
              false ∎
            y-in-F : fst (F y)
            y-in-F = snd (snd (F-wit y)) (λ n →
              f-pred n x     ≡⟨ sym (f-prop n x) ⟩
              fst x (f-elem n) ≡⟨ f-false n ⟩
              false ∎)
            y-in-G : fst (G y)
            y-in-G = snd (snd (G-wit y)) (λ n →
              g-pred n x     ≡⟨ sym (g-prop n x) ⟩
              fst x (g-elem n) ≡⟨ g-false n ⟩
              false ∎)
        in disjoint y y-in-F y-in-G

      -- 0 ≡ 1 in B/d
      0≡1 : BooleanRingStr.𝟘 (snd (fst B/d-Booleω)) ≡ BooleanRingStr.𝟙 (snd (fst B/d-Booleω))
      0≡1 = SpectrumEmptyImpliesTrivial.0≡1-in-B sd-axiom B/d-Booleω spEmpty

      -- Use general IdealBound module
      open IdealBound (fst B) d

      private
        𝟙B = BooleanRingStr.𝟙 (snd (fst B))
        𝟘B = BooleanRingStr.𝟘 (snd (fst B))
        _∨B_ = BooleanAlgebraStr._∨_ (fst B)
        R = BooleanRing→CommRing (fst B)
        module CRS = CommRingStr (snd R)
        _·B_ = CRS._·_
        _+B_ = CRS._+_
        fJ = finJoinBR (fst B) d

      idealMem : ∥ isInIdeal R d CRS.1r ∥₁
      idealMem = idealDecomp R d CRS.1r (0≡1-quotient→1∈ideal (fst B) d 0≡1)

      -- Filter d to g-contributions and f-contributions
      gPartOfD : ℕ → ⟨ fst B ⟩
      gPartOfD zero = 𝟘B
      gPartOfD (suc n) = ⊎.rec (λ _ → gPartOfD n) (λ k → g-elem k ∨B gPartOfD n) (decode n)

      fPartOfD : ℕ → ⟨ fst B ⟩
      fPartOfD zero = 𝟘B
      fPartOfD (suc n) = ⊎.rec (λ j → f-elem j ∨B fPartOfD n) (λ _ → fPartOfD n) (decode n)

      private
        _∨Bool_ = BooleanAlgebraStr._∨_ BoolBR

      -- Split: fJ n = fPartOfD n ∨ gPartOfD n
      fJ-split : (n : ℕ) → fJ n ≡ fPartOfD n ∨B gPartOfD n
      fJ-split zero = sym BA.∨IdL
      fJ-split (suc n) with decode n
      ... | ⊎.inl j =
        f-elem j ∨B fJ n
          ≡⟨ cong (f-elem j ∨B_) (fJ-split n) ⟩
        f-elem j ∨B (fPartOfD n ∨B gPartOfD n)
          ≡⟨ BA.∨Assoc ⟩
        (f-elem j ∨B fPartOfD n) ∨B gPartOfD n ∎
      ... | ⊎.inr k =
        g-elem k ∨B fJ n
          ≡⟨ cong (g-elem k ∨B_) (fJ-split n) ⟩
        g-elem k ∨B (fPartOfD n ∨B gPartOfD n)
          ≡⟨ BA.∨Assoc ⟩
        (g-elem k ∨B fPartOfD n) ∨B gPartOfD n
          ≡⟨ cong (_∨B gPartOfD n) BA.∨Comm ⟩
        (fPartOfD n ∨B g-elem k) ∨B gPartOfD n
          ≡⟨ sym BA.∨Assoc ⟩
        fPartOfD n ∨B (g-elem k ∨B gPartOfD n) ∎

      -- BoolHom preserves ∨
      boolhom-∨ : (x : Sp B) (a b : ⟨ fst B ⟩) → fst x (a ∨B b) ≡ fst x a ∨Bool fst x b
      boolhom-∨ x a b =
        let _+S_ = CommRingStr._+_ (snd (BooleanRing→CommRing BoolBR))
        in fst x (a ∨B b)
          ≡⟨ IsCommRingHom.pres+ (snd x) (a +B b) (a ·B b) ⟩
        fst x (a +B b) +S fst x (a ·B b)
          ≡⟨ cong₂ _+S_ (IsCommRingHom.pres+ (snd x) a b) (IsCommRingHom.pres· (snd x) a b) ⟩
        fst x a ∨Bool fst x b ∎

      -- BoolHom maps gPartOfD to false when all g-elements map to false
      gPartOfD-false : (x : Sp B) → ((k : ℕ) → fst x (g-elem k) ≡ false)
                     → (n : ℕ) → fst x (gPartOfD n) ≡ false
      gPartOfD-false x _ zero = IsCommRingHom.pres0 (snd x)
      gPartOfD-false x gf (suc n) with decode n
      ... | ⊎.inl _ = gPartOfD-false x gf n
      ... | ⊎.inr k =
        fst x (g-elem k ∨B gPartOfD n)
          ≡⟨ boolhom-∨ x (g-elem k) (gPartOfD n) ⟩
        fst x (g-elem k) ∨Bool fst x (gPartOfD n)
          ≡⟨ cong₂ _∨Bool_ (gf k) (gPartOfD-false x gf n) ⟩
        false ∎

      -- BoolHom maps fPartOfD to false when all f-elements map to false
      fPartOfD-false : (x : Sp B) → ((j : ℕ) → fst x (f-elem j) ≡ false)
                     → (n : ℕ) → fst x (fPartOfD n) ≡ false
      fPartOfD-false x _ zero = IsCommRingHom.pres0 (snd x)
      fPartOfD-false x ff (suc n) with decode n
      ... | ⊎.inl j =
        fst x (f-elem j ∨B fPartOfD n)
          ≡⟨ boolhom-∨ x (f-elem j) (fPartOfD n) ⟩
        fst x (f-elem j) ∨Bool fst x (fPartOfD n)
          ≡⟨ cong₂ _∨Bool_ (ff j) (fPartOfD-false x ff n) ⟩
        false ∎
      ... | ⊎.inr _ = fPartOfD-false x ff n

      -- From isInIdeal, construct separator
      fromIdeal : isInIdeal R d (CommRingStr.1r (snd R))
                → ∥ Σ[ D ∈ DecSubsetOfStone S ] (ClosedSubDec S (F , F-closed) D) × (ClosedSubNotDec S (G , G-closed) D) ∥₁
      fromIdeal iI = ∣ D , D-sep-F , D-sep-G ∣₁
        where
        N = fst (idealBound iI)
        fJ-eq : fJ N ≡ 𝟙B
        fJ-eq =
          fJ N        ≡⟨ sym (CRS.·IdL (fJ N)) ⟩
          𝟙B ·B fJ N ≡⟨ snd (idealBound iI) ⟩
          𝟙B ∎

        D : DecSubsetOfStone S
        D y = fst (transport (sym SpB≡S) y) (gPartOfD N)

        D-sep-G : ClosedSubNotDec S (G , G-closed) D
        D-sep-G y y∈G = gPartOfD-false x g-false' N
          where
          x = transport (sym SpB≡S) y
          g-false' : (k : ℕ) → fst x (g-elem k) ≡ false
          g-false' k =
            fst x (g-elem k) ≡⟨ g-prop k x ⟩
            g-pred k x        ≡⟨ fst (snd (G-wit (transport SpB≡S x)))
                                   (subst (λ z → fst (G z)) (sym (transportTransport⁻ SpB≡S y)) y∈G) k ⟩
            false ∎

        D-sep-F : ClosedSubDec S (F , F-closed) D
        D-sep-F y y∈F =
          let x = transport (sym SpB≡S) y
              f-false' : (j : ℕ) → fst x (f-elem j) ≡ false
              f-false' j =
                fst x (f-elem j) ≡⟨ f-prop j x ⟩
                f-pred j x        ≡⟨ fst (snd (F-wit (transport SpB≡S x)))
                                       (subst (λ z → fst (F z)) (sym (transportTransport⁻ SpB≡S y)) y∈F) j ⟩
                false ∎
          in fst x (gPartOfD N)
            ≡⟨ sym (BooleanAlgebraStr.∨IdL BoolBR) ⟩
          false ∨Bool fst x (gPartOfD N)
            ≡⟨ cong (_∨Bool fst x (gPartOfD N)) (sym (fPartOfD-false x f-false' N)) ⟩
          fst x (fPartOfD N) ∨Bool fst x (gPartOfD N)
            ≡⟨ sym (boolhom-∨ x (fPartOfD N) (gPartOfD N)) ⟩
          fst x (fPartOfD N ∨B gPartOfD N)
            ≡⟨ cong (fst x) (sym (fJ-split N)) ⟩
          fst x (fJ N)
            ≡⟨ cong (fst x) fJ-eq ⟩
          fst x 𝟙B
            ≡⟨ IsCommRingHom.pres1 (snd x) ⟩
          true ∎

-- StoneAsClosedSubsetOfCantor (tex Lemma 2082)
module CantorIsStoneModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; SpGeneralBooleanRing)
  open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; freeBA-universal-property)
  import QuotientBool as QB
  open import CommRingQuotients.IdealTerms using (isInIdeal; isImage; iszero; isSum; isMul; idealDecomp)
  open import CommRingQuotients.TrivialIdeal using (quotientFiber)
  import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
  open import Cubical.Algebra.CommRing.Quotient.Base using (quotientHomSurjective)
  open import Cubical.HITs.PropositionalTruncation as PT
  open import Cubical.Data.Sigma using (Σ≡Prop)
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
    fiberProp c (x , qx=c) (y , qy=c) = Σ≡Prop (λ d → CommRingStr.is-set (snd R') _ _) help'' where
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

-- MapsStoneToNareBounded (tex Lemma 1568)
module MapsStoneToNareBoundedModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isSetBoolHom)
  open StoneClosedSubsetsModule
  open SDDecToElemModule
  open import Cubical.Data.Bool using (Dec→Bool; true≢false; false≢true)
  open import Cubical.Data.Nat.Properties using (discreteℕ)
  open import Cubical.Foundations.Equiv using (equivFun)
  open import Cubical.Foundations.Transport using (transportTransport⁻)
  open import Cubical.Algebra.CommRing using (IsCommRingHom)
  open import Cubical.Data.Nat.Order using (_≤_; _<_; splitℕ-<; <≤-trans; ≤-suc; <→≢)
  open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
  import QuotientBool as QB
  import Cubical.Data.Sum as ⊎

  private
    Dec→Bool-yes : ∀ {ℓ'} {P : Type ℓ'} (dc : Dec P) → P → Dec→Bool dc ≡ true
    Dec→Bool-yes (yes _) _ = refl
    Dec→Bool-yes (no ¬p) p = Empty.rec (¬p p)

    Dec→Bool-false : ∀ {ℓ'} {P : Type ℓ'} (dc : Dec P) → ¬ P → Dec→Bool dc ≡ false
    Dec→Bool-false (yes p) ¬p = Empty.rec (¬p p)
    Dec→Bool-false (no _) _ = refl

    _∨Bool_ = BooleanAlgebraStr._∨_ BoolBR

    boolhom-∨ : (B' : Booleω) (x : Sp B') (a b : ⟨ fst B' ⟩)
      → fst x (BooleanAlgebraStr._∨_ (fst B') a b) ≡ fst x a ∨Bool fst x b
    boolhom-∨ B' x a b =
      let _+S_ = CommRingStr._+_ (snd (BooleanRing→CommRing BoolBR))
          _+B'_ = CommRingStr._+_ (snd (BooleanRing→CommRing (fst B')))
          _·B'_ = CommRingStr._·_ (snd (BooleanRing→CommRing (fst B')))
      in fst x (BooleanAlgebraStr._∨_ (fst B') a b)
        ≡⟨ IsCommRingHom.pres+ (snd x) (a +B' b) (a ·B' b) ⟩
      fst x (a +B' b) +S fst x (a ·B' b)
        ≡⟨ cong₂ _+S_ (IsCommRingHom.pres+ (snd x) a b)
                       (IsCommRingHom.pres· (snd x) a b) ⟩
      fst x a ∨Bool fst x b ∎

    joinAllFalse : (B' : Booleω) (d' : ℕ → ⟨ fst B' ⟩) (x : Sp B') (N : ℕ)
      → ((n : ℕ) → n < N → fst x (d' n) ≡ false)
      → fst x (finJoinBR (fst B') d' N) ≡ false
    joinAllFalse B' d' x zero _ = IsCommRingHom.pres0 (snd x)
    joinAllFalse B' d' x (suc N) allF =
      fst x (BooleanAlgebraStr._∨_ (fst B') (d' N) (finJoinBR (fst B') d' N))
        ≡⟨ boolhom-∨ B' x (d' N) (finJoinBR (fst B') d' N) ⟩
      fst x (d' N) ∨Bool fst x (finJoinBR (fst B') d' N)
        ≡⟨ cong₂ _∨Bool_ (allF N (0 , refl)) (joinAllFalse B' d' x N (λ n h → allF n (≤-suc h))) ⟩
      false ∎

  MapsStoneToNareBounded : (S : Stone) → (f : fst S → ℕ)
    → ∥ Σ[ N ∈ ℕ ] ((s : fst S) → f s < N) ∥₁
  MapsStoneToNareBounded S f = PT.map mainProof (extract-finJoin-bound 0≡1)
    where
    |S| = fst S
    B : Booleω
    B = fst (snd S)
    SpB≡S = snd (snd S)

    fiber-pred : ℕ → Sp B → Bool
    fiber-pred n x = Dec→Bool (discreteℕ (f (transport SpB≡S x)) n)

    d : ℕ → ⟨ fst B ⟩
    d n = elemFromDecPred sd-axiom B (fiber-pred n)

    d-property : (n : ℕ) (x : Sp B) → fst x (d n) ≡ fiber-pred n x
    d-property n x = decPred-elem-correspondence sd-axiom B (fiber-pred n) x

    open IdealBound (fst B) d

    B/d-Booleω : Booleω
    B/d-Booleω = fst B QB./Im d , quotientBySeqHasBooleω B d

    spEmpty : Sp B/d-Booleω → ⊥
    spEmpty sp-hom =
      let open SpOfQuotientBySeq (fst B) d using (Sp-quotient-≃)
          (x , allZero) = equivFun Sp-quotient-≃ sp-hom
          y = transport SpB≡S x
          m = f y
      in true≢false (sym (d-property m x ∙ Dec→Bool-yes (discreteℕ m m) refl) ∙ allZero m)

    0≡1 : BooleanRingStr.𝟘 (snd (fst B/d-Booleω)) ≡ BooleanRingStr.𝟙 (snd (fst B/d-Booleω))
    0≡1 = SpectrumEmptyImpliesTrivial.0≡1-in-B sd-axiom B/d-Booleω spEmpty

    mainProof : Σ[ N ∈ ℕ ] finJoinBR (fst B) d N ≡ BooleanRingStr.𝟙 (snd (fst B))
      → Σ[ N ∈ ℕ ] ((s : |S|) → f s < N)
    mainProof (N , fJ≡1) = suc N , bound
      where
      bound : (s : |S|) → f s < suc N
      bound s with splitℕ-< (f s) N
      ... | ⊎.inl fs<N = ≤-suc fs<N
      ... | ⊎.inr N≤fs = Empty.rec (true≢false (sym fJ-true ∙ fJ-false))
        where
        x : Sp B
        x = transport (sym SpB≡S) s
        m = f (transport SpB≡S x)
        N≤m : N ≤ m
        N≤m = subst (N ≤_) (sym (cong f (transportTransport⁻ SpB≡S s))) N≤fs

        fJ-true : fst x (finJoinBR (fst B) d N) ≡ true
        fJ-true =
          fst x (finJoinBR (fst B) d N)
            ≡⟨ cong (fst x) fJ≡1 ⟩
          fst x (BooleanRingStr.𝟙 (snd (fst B)))
            ≡⟨ IsCommRingHom.pres1 (snd x) ⟩
          true ∎

        all-false : (n : ℕ) → n < N → fst x (d n) ≡ false
        all-false n n<N =
          fst x (d n)
            ≡⟨ d-property n x ⟩
          Dec→Bool (discreteℕ m n)
            ≡⟨ Dec→Bool-false (discreteℕ m n) (λ m≡n → <→≢ (<≤-trans n<N N≤m) (sym m≡n)) ⟩
          false ∎

        fJ-false : fst x (finJoinBR (fst B) d N) ≡ false
        fJ-false = joinAllFalse B d x N all-false
