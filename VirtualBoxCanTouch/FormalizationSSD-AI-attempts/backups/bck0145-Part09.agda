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
open import Cubical.Data.Nat using (ℕ; suc; zero) renaming (_+_ to _+ℕ_; _∸_ to _∸ℕ_)
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

  -- Truncated choice for families of closed propositions over Stone spaces.
  -- Derivable from localChoice-axiom via the StoneClosedSubsets equivalence
  -- (tex Theorem StoneClosedSubsets, (v)→(i) direction), but the full
  -- derivation requires implementing additional machinery.
  -- Replaces the false extractClosedProp which used isPropIsClosedPropBare.
  postulate
    closedFamilyChoice : (S : Stone) (A : fst S → hProp ℓ-zero)
      → ((x : fst S) → isClosedProp (A x))
      → ∥ ((x : fst S) → Σ[ α ∈ binarySequence ] ⟨ A x ⟩ ↔ ((n : ℕ) → α n ≡ false)) ∥₁

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
  import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
  open import CommRingQuotients.IdealTerms using (isInIdeal; isImage; iszero; isSum; isMul; idealDecomp)
  open import CommRingQuotients.TrivialIdeal using (trivialQuotient→1∈I)
  import QuotientBool as QB
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

  -- Opaque bridge: 0≡1 in BooleanRing quotient → 1 in CommRing ideal
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

      -- 1 ∈ ideal(d) in the CommRing of B
      1∈ideal : IQ.generatedIdeal (BooleanRing→CommRing (fst B)) d
                  (CommRingStr.1r (snd (BooleanRing→CommRing (fst B))))
      1∈ideal = 0≡1-quotient→1∈ideal (fst B) d 0≡1

      -- Extract isInIdeal from the HIT
      idealMem : ∥ isInIdeal (BooleanRing→CommRing (fst B)) d
                     (CommRingStr.1r (snd (BooleanRing→CommRing (fst B)))) ∥₁
      idealMem = idealDecomp (BooleanRing→CommRing (fst B)) d _ 1∈ideal

      -- Ring abbreviations
      private
        R = BooleanRing→CommRing (fst B)
        module CRS = CommRingStr (snd R)
        𝟘B = BooleanRingStr.𝟘 (snd (fst B))
        𝟙B = BooleanRingStr.𝟙 (snd (fst B))
        _∨B_ = BA._∨_
        _·B_ = CRS._·_
        _+B_ = CRS._+_
        fJ = finJoinBR (fst B)

      -- r ≤ fJ d N → r ≤ fJ d (suc N)
      leq-suc : {r : ⟨ fst B ⟩} (N : ℕ) → r ·B fJ d N ≡ r → r ·B fJ d (suc N) ≡ r
      leq-suc {r} N p =
        r ·B (d N ∨B fJ d N)
          ≡⟨ sym (cong (_·B (d N ∨B fJ d N)) p) ⟩
        (r ·B fJ d N) ·B (d N ∨B fJ d N)
          ≡⟨ sym (CRS.·Assoc r (fJ d N) (d N ∨B fJ d N)) ⟩
        r ·B (fJ d N ·B (d N ∨B fJ d N))
          ≡⟨ cong (r ·B_) (cong (fJ d N ·B_) BA.∨Comm) ⟩
        r ·B (fJ d N ·B (fJ d N ∨B d N))
          ≡⟨ cong (r ·B_) BA.∧AbsorbL∨ ⟩
        r ·B fJ d N
          ≡⟨ p ⟩
        r ∎

      -- r ≤ fJ d N → r ≤ fJ d (N + k) (by repeated leq-suc)
      leq-extend : {r : ⟨ fst B ⟩} (N k : ℕ) → r ·B fJ d N ≡ r → r ·B fJ d (k +ℕ N) ≡ r
      leq-extend N zero p = p
      leq-extend N (suc k) p = leq-suc (k +ℕ N) (leq-extend N k p)

      leq-max-left : {r : ⟨ fst B ⟩} (N₁ N₂ : ℕ) → r ·B fJ d N₁ ≡ r → r ·B fJ d (max N₁ N₂) ≡ r
      leq-max-left {r} N₁ N₂ p =
        subst (λ M → r ·B fJ d M ≡ r) (≤-∸-+-cancel {N₁} {max N₁ N₂} (left-≤-max {N₁} {N₂}))
              (leq-extend N₁ (max N₁ N₂ ∸ℕ N₁) p)
        where open import Cubical.Data.Nat.Order using (left-≤-max; ≤-∸-+-cancel)

      leq-max-right : {r : ⟨ fst B ⟩} (N₁ N₂ : ℕ) → r ·B fJ d N₂ ≡ r → r ·B fJ d (max N₁ N₂) ≡ r
      leq-max-right {r} N₁ N₂ p =
        subst (λ M → r ·B fJ d M ≡ r) (≤-∸-+-cancel {N₂} {max N₁ N₂} (right-≤-max {N₂} {N₁}))
              (leq-extend N₂ (max N₁ N₂ ∸ℕ N₂) p)
        where open import Cubical.Data.Nat.Order using (right-≤-max; ≤-∸-+-cancel)

      -- From isInIdeal, extract bound N such that r · finJoinBR d N ≡ r
      idealBound : {r : ⟨ fst B ⟩} → isInIdeal R d r
                 → Σ[ N ∈ ℕ ] (r ·B fJ d N ≡ r)
      idealBound (isImage r n p) = suc n ,
        (r ·B (d n ∨B fJ d n)
          ≡⟨ cong (λ z → z ·B (d n ∨B fJ d n)) (sym p) ⟩
        d n ·B (d n ∨B fJ d n)
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
          (r ·B fJ d M
            ≡⟨ cong (_·B fJ d M) r=s+t ⟩
          (s +B t) ·B fJ d M
            ≡⟨ CRS.·Comm (s +B t) (fJ d M) ⟩
          fJ d M ·B (s +B t)
            ≡⟨ CRS.·DistR+ (fJ d M) s t ⟩
          (fJ d M ·B s) +B (fJ d M ·B t)
            ≡⟨ cong₂ _+B_ (CRS.·Comm (fJ d M) s) (CRS.·Comm (fJ d M) t) ⟩
          (s ·B fJ d M) +B (t ·B fJ d M)
            ≡⟨ cong₂ _+B_ p₁' p₂' ⟩
          s +B t
            ≡⟨ sym r=s+t ⟩
          r ∎)
      idealBound (isMul r s t r=st tI) =
        let (N , p) = idealBound tI
        in N ,
          (r ·B fJ d N
            ≡⟨ cong (_·B fJ d N) r=st ⟩
          (s ·B t) ·B fJ d N
            ≡⟨ sym (CRS.·Assoc s t (fJ d N)) ⟩
          s ·B (t ·B fJ d N)
            ≡⟨ cong (s ·B_) p ⟩
          s ·B t
            ≡⟨ sym r=st ⟩
          r ∎)

      -- Filter d to g-contributions and f-contributions
      gPartOfD : ℕ → ⟨ fst B ⟩
      gPartOfD zero = 𝟘B
      gPartOfD (suc n) = ⊎.rec (λ _ → gPartOfD n) (λ k → g-elem k ∨B gPartOfD n) (decode n)

      fPartOfD : ℕ → ⟨ fst B ⟩
      fPartOfD zero = 𝟘B
      fPartOfD (suc n) = ⊎.rec (λ j → f-elem j ∨B fPartOfD n) (λ _ → fPartOfD n) (decode n)

      private
        _∨Bool_ = BooleanAlgebraStr._∨_ BoolBR

      -- Split: fJ d n = fPartOfD n ∨ gPartOfD n
      fJ-split : (n : ℕ) → fJ d n ≡ fPartOfD n ∨B gPartOfD n
      fJ-split zero = sym BA.∨IdL
      fJ-split (suc n) with decode n
      ... | ⊎.inl j =
        f-elem j ∨B fJ d n
          ≡⟨ cong (f-elem j ∨B_) (fJ-split n) ⟩
        f-elem j ∨B (fPartOfD n ∨B gPartOfD n)
          ≡⟨ BA.∨Assoc ⟩
        (f-elem j ∨B fPartOfD n) ∨B gPartOfD n ∎
      ... | ⊎.inr k =
        g-elem k ∨B fJ d n
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
        fJ-eq : fJ d N ≡ 𝟙B
        fJ-eq =
          fJ d N        ≡⟨ sym (CRS.·IdL (fJ d N)) ⟩
          𝟙B ·B fJ d N ≡⟨ snd (idealBound iI) ⟩
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
          fst x (fJ d N)
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
