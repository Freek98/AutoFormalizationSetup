-- Under LLPO: the hard half of de Morgan for open propositions, and the headline
-- consequence that a disjunction of *closed* propositions is closed.
--
-- The reusable, LLPO-free ingredients live in two sibling project modules
-- (candidates for promotion into the FormalizationSSD library):
--   * ClosedNegationOpen
--        - all0↔¬Σℕ                    "all zero" is the negation of "has a one"
--        - closedWitness→negOpenWitness  a closed prop is the negation of an open one
--        - closedIsNegationOfOpenProp    (truncated form of the above)
--        - deMorganEasy                  ¬P ⊔ ¬Q → ¬(P ⊓ Q)            (no LLPO)
--        - isClosedProp-↔ , ⊔-cong↔ , ↔-trans   transport closedness along ↔
--   * AtMostOnce
--        - firstHitOnly + at-most-once   every open prop has an at-most-once witness
--        - Interleave.combine            α on the evens, β on the odds
--
-- so this file only assembles the three results the development is about:
--   (1) deMorganHard / deMorganOpen   de Morgan for open propositions, and
--   (2) disjunctionClosed             closed propositions are closed under ⊔,
-- the latter being  P,Q closed  ⇒  P = ¬P′, Q = ¬Q′ (P′,Q′ open)
--                              ⇒  P ⊔ Q ↔ ¬P′ ⊔ ¬Q′ ↔ ¬(P′ ⊓ Q′)  (de Morgan)
--                              ⇒  ¬(open) is closed.
module DisjunctionClosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; doubleℕ)
open import Cubical.Data.Bool using (true ; false ; true≢false)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Functions.Logic using (¬_ ; _⊔_ ; _⊓_ ; ⇔toPath)

open import BasicDefinitions using (binarySequence ; Σℕ ; _↔_)
open import PropositionalTopology.Definitions
open import PropositionalTopology.Properties using (Open⊓ ; negOpenIsClosed)
open import AtMostOnce
open import ClosedNegationOpen

open import OmnisciencePrinciples.LLPO using (LLPO ; LLPOExplicitAt)
open import StoneSpaces.Examples.Ninfty using (ℕ∞ ; hits1AtMostOnce)
open import LLMGeneratedFixes.Parity using (even-or-odd)

-- The sequence-level core "closed = ¬ open" the rewrite started from is now
-- PropositionalTopology.ClosedNegationOpen.all0↔¬Σℕ.

module assumingLLPO (llpo : LLPO) where
  open Interleave  -- combine , fstOnEvens , sndOnOdds , evenHit , oddHit

  ------------------------------------------------------------------------
  -- de Morgan, hard half (LLPO).
  --
  -- Witnessed core: at-most-once open witnesses α (for P), β (for Q), and a
  -- proof of ¬(P ⊓ Q).  Interleave α,β into γ.  γ hits 1 at most once — two
  -- even hits agree by α's uniqueness, two odd hits by β's, and a mixed hit
  -- would yield ⟨P⟩∧⟨Q⟩, impossible.  So γ ∈ ℕ∞ and LLPO gives "evens all 0"
  -- (⇒ ¬P, since γ(2n)=αn) or "odds all 0" (⇒ ¬Q).
  ------------------------------------------------------------------------
  module DeMorganHardWitnessed
    (P Q : hProp ℓ-zero)
    (amP : isAtMostOnceOpenWitness P)
    (amQ : isAtMostOnceOpenWitness Q)
    (¬pq : ⟨ ¬ (P ⊓ Q) ⟩) where

    α : binarySequence
    α = fst amP
    αOnce : hits1AtMostOnce α
    αOnce = fst (snd amP)
    P↔Σα : ⟨ P ⟩ ↔ Σℕ α
    P↔Σα = snd (snd amP)

    β : binarySequence
    β = fst amQ
    βOnce : hits1AtMostOnce β
    βOnce = fst (snd amQ)
    Q↔Σβ : ⟨ Q ⟩ ↔ Σℕ β
    Q↔Σβ = snd (snd amQ)

    γ : binarySequence
    γ = combine α β

    γAtMostOnce : hits1AtMostOnce γ
    γAtMostOnce n m γn γm with even-or-odd n | even-or-odd m
    ... | inl (a , n≡2a)   | inl (b , m≡2b)   =
            n≡2a ∙ cong doubleℕ (αOnce a b (evenHit α β n a n≡2a γn) (evenHit α β m b m≡2b γm)) ∙ sym m≡2b
    ... | inl (a , n≡2a)   | inr (b , m≡2b+1) =
            Empty.rec (¬pq ( snd P↔Σα (a , evenHit α β n a n≡2a γn)
                           , snd Q↔Σβ (b , oddHit α β m b m≡2b+1 γm) ))
    ... | inr (a , n≡2a+1) | inl (b , m≡2b)   =
            Empty.rec (¬pq ( snd P↔Σα (b , evenHit α β m b m≡2b γm)
                           , snd Q↔Σβ (a , oddHit α β n a n≡2a+1 γn) ))
    ... | inr (a , n≡2a+1) | inr (b , m≡2b+1) =
            n≡2a+1 ∙ cong (λ k → suc (doubleℕ k)) (βOnce a b (oddHit α β n a n≡2a+1 γn) (oddHit α β m b m≡2b+1 γm)) ∙ sym m≡2b+1

    concl : LLPOExplicitAt (γ , γAtMostOnce) → ⟨ ¬ P ⟩ ⊎ ⟨ ¬ Q ⟩
    concl (inl evensFalse) = inl λ p →
      let (n , αn) = fst P↔Σα p
      in true≢false (sym αn ∙ sym (fstOnEvens α β n) ∙ evensFalse n)
    concl (inr oddsFalse) = inr λ q →
      let (n , βn) = fst Q↔Σβ q
      in true≢false (sym βn ∙ sym (sndOnOdds α β n) ∙ oddsFalse n)

    result : ⟨ ¬ P ⊔ ¬ Q ⟩
    result = PT.map concl (llpo (γ , γAtMostOnce))

  -- truncated wrapper: present P,Q by at-most-once witnesses, then apply the core
  deMorganHard : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
               → ⟨ ¬ (P ⊓ Q) ⟩ → ⟨ ¬ P ⊔ ¬ Q ⟩
  deMorganHard P Q oP oQ ¬pq =
    PT.rec2 (snd (¬ P ⊔ ¬ Q))
      (λ amP amQ → DeMorganHardWitnessed.result P Q amP amQ ¬pq)
      (openProp→atMostOnceProp P oP)
      (openProp→atMostOnceProp Q oQ)

  -- de Morgan for open propositions, both halves.
  deMorganOpen : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
               → ⟨ ¬ P ⊔ ¬ Q ⟩ ↔ ⟨ ¬ (P ⊓ Q) ⟩
  deMorganOpen P Q oP oQ = deMorganEasy P Q , deMorganHard P Q oP oQ

  -- Same statement as a propositional equality (both sides are hProps).
  deMorganOpen≡ : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
                → (¬ P ⊔ ¬ Q) ≡ ¬ (P ⊓ Q)
  deMorganOpen≡ P Q oP oQ = ⇔toPath (deMorganEasy P Q) (deMorganHard P Q oP oQ)

  ------------------------------------------------------------------------
  -- Headline: closed propositions are closed under disjunction.
  --
  -- Pick open P′,Q′ with P = ¬P′, Q = ¬Q′.  Then
  --   P ⊔ Q  ↔  ¬P′ ⊔ ¬Q′  ↔  ¬(P′ ⊓ Q′)
  -- and ¬(P′ ⊓ Q′) is closed because P′ ⊓ Q′ is open.
  ------------------------------------------------------------------------

  -- the per-witness step, factored out of the truncation elimination
  disjunctionClosedStep : (P Q : hProp ℓ-zero)
    → (Σ[ P′ ∈ hProp ℓ-zero ] isOpenWitness P′ × (⟨ P ⟩ ↔ ⟨ ¬ P′ ⟩))
    → (Σ[ Q′ ∈ hProp ℓ-zero ] isOpenWitness Q′ × (⟨ Q ⟩ ↔ ⟨ ¬ Q′ ⟩))
    → isClosedProp (P ⊔ Q)
  disjunctionClosedStep P Q (P′ , owP′ , P↔¬P′) (Q′ , owQ′ , Q↔¬Q′) =
    isClosedProp-↔ (P ⊔ Q) (¬ (P′ ⊓ Q′))
      (↔-trans (⊔-cong↔ P (¬ P′) Q (¬ Q′) P↔¬P′ Q↔¬Q′)
               (deMorganOpen P′ Q′ ∣ owP′ ∣₁ ∣ owQ′ ∣₁))
      (negOpenIsClosed (P′ ⊓ Q′) (Open⊓ P′ Q′ ∣ owP′ ∣₁ ∣ owQ′ ∣₁))

  disjunctionClosed : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
                    → isClosedProp (P ⊔ Q)
  disjunctionClosed P Q cP cQ =
    PT.rec2 squash₁ (disjunctionClosedStep P Q)
      (closedIsNegationOfOpenProp P cP)
      (closedIsNegationOfOpenProp Q cQ)

  -- packaged on the type `Closed = Σ hProp isClosedProp`
  Closed⊔ : (P Q : Closed) → isClosedProp (fst P ⊔ fst Q)
  Closed⊔ (P , cP) (Q , cQ) = disjunctionClosed P Q cP cQ

  ------------------------------------------------------------------------
  -- Alternative formulation of the final step, for comparison.
  --
  -- OPTION A (above, `disjunctionClosedStep` / `disjunctionClosed`):
  --   transport closedness along the equivalence with the *explicit witness
  --   transport* `isClosedProp-↔`.  Stays at the level of ↔ throughout.
  --
  -- OPTION B (below, primed):
  --   turn the equivalence of hProps into an actual *equality* with `⇔toPath`
  --   (propositional univalence) and transport with `subst isClosedProp`.
  --   Shorter, but pulls in propositional extensionality.
  -- Keep whichever reads better; they prove the same statement.
  ------------------------------------------------------------------------
  disjunctionClosedStep′ : (P Q : hProp ℓ-zero)
    → (Σ[ P′ ∈ hProp ℓ-zero ] isOpenWitness P′ × (⟨ P ⟩ ↔ ⟨ ¬ P′ ⟩))
    → (Σ[ Q′ ∈ hProp ℓ-zero ] isOpenWitness Q′ × (⟨ Q ⟩ ↔ ⟨ ¬ Q′ ⟩))
    → isClosedProp (P ⊔ Q)
  disjunctionClosedStep′ P Q (P′ , owP′ , P↔¬P′) (Q′ , owQ′ , Q↔¬Q′) =
    subst isClosedProp (sym P⊔Q≡¬⊓)
      (negOpenIsClosed (P′ ⊓ Q′) (Open⊓ P′ Q′ ∣ owP′ ∣₁ ∣ owQ′ ∣₁))
    where
      chain : ⟨ P ⊔ Q ⟩ ↔ ⟨ ¬ (P′ ⊓ Q′) ⟩
      chain = ↔-trans (⊔-cong↔ P (¬ P′) Q (¬ Q′) P↔¬P′ Q↔¬Q′)
                      (deMorganOpen P′ Q′ ∣ owP′ ∣₁ ∣ owQ′ ∣₁)
      P⊔Q≡¬⊓ : (P ⊔ Q) ≡ ¬ (P′ ⊓ Q′)
      P⊔Q≡¬⊓ = ⇔toPath (fst chain) (snd chain)

  disjunctionClosed′ : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
                     → isClosedProp (P ⊔ Q)
  disjunctionClosed′ P Q cP cQ =
    PT.rec2 squash₁ (disjunctionClosedStep′ P Q)
      (closedIsNegationOfOpenProp P cP)
      (closedIsNegationOfOpenProp Q cQ)
