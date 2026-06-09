-- "A closed proposition is the negation of an open one", in three layers, plus the
-- easy half of de Morgan and the closure of open/closed under logical equivalence.
--
-- All of this is LLPO-free.  The LLPO content (the *hard* half of de Morgan and the
-- consequence that closed propositions are closed under ⊔) lives in the project file
-- DisjunctionClosed, which is assembled out of the lemmas here.
--
-- Negation appears at two levels, and we keep them notationally distinct:
--   ¬ᵗ_  : Type ℓ → Type ℓ        the ordinary negation A → ⊥   (Cubical.Relation.Nullary)
--   ¬_   : hProp ℓ → hProp ℓ      the propositional negation     (Cubical.Functions.Logic)
-- The sequence-level core (§1) is naturally stated with ¬ᵗ_; the hProp statements
-- (§2,§3) with ¬_.
--
-- Kept in the project (rather than the shared FormalizationSSD library, which is synced
-- via git); could be promoted to the library later.
module ClosedNegationOpen where

open import BasicDefinitions                       -- binarySequence , Σℕ , _↔_
open import BinarySequences.Properties using (module AtMostOneHit)  -- extract (was: module extractFirstHitInBinarySequence)
open import PropositionalTopology.Definitions      -- isOpenWitness , isClosedWitness , isOpenProp , isClosedProp
open import PropositionalTopology.Properties using (negOpenWitnessIsClosedWitness)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (true ; false ; true≢false ; ¬true→false)
open import Cubical.Data.Sigma
import Cubical.Data.Sum as ⊎
import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Cubical.Functions.Logic using (¬_ ; _⊔_ ; _⊓_ ; ⊥)
open import Cubical.Relation.Nullary using () renaming (¬_ to ¬ᵗ_)

------------------------------------------------------------------------
-- §1  Sequence level: "all zero" is the negation of "has a one".
--
-- This is the explicit heart of the duality.  `Σℕ α` is the open predicate
-- ("α hits 1 somewhere"); `(∀ n → α n ≡ false)` is the closed predicate.
-- They are negations of each other (the ¬ here is the ordinary type-level one).
------------------------------------------------------------------------

module _ (α : binarySequence) where
  all0→¬Σℕ : (∀ n → α n ≡ false) → ¬ᵗ (Σℕ α)
  all0→¬Σℕ all0 (n , αn≡true) = true≢false (sym αn≡true ∙ all0 n)

  ¬Σℕ→all0 : ¬ᵗ (Σℕ α) → (∀ n → α n ≡ false)
  ¬Σℕ→all0 no-hit n = ¬true→false (α n) (λ αn≡true → no-hit (n , αn≡true))

  all0↔¬Σℕ : (∀ n → α n ≡ false) ↔ (¬ᵗ (Σℕ α))
  all0↔¬Σℕ = all0→¬Σℕ , ¬Σℕ→all0

------------------------------------------------------------------------
-- §2  Witness level: a closed witness of P yields an open Q with P ↔ ¬ Q.
--
-- Q is "α hits a one" (truncated so it is a proposition); α is the very
-- sequence from the closed witness.  ¬ Q is then closed with the same
-- witness α (negOpenWitnessIsClosedWitness), and P ↔ ¬ Q because both are
-- equivalent to "α is all zero".
------------------------------------------------------------------------

module ClosedWitnessIsNegOpen (P : hProp ℓ-zero) (cw : isClosedWitness P) where
  α : binarySequence
  α = fst cw

  P↔all0 : ⟨ P ⟩ ↔ (∀ n → α n ≡ false)
  P↔all0 = snd cw

  open AtMostOneHit α using (extract)

  -- the open proposition dual to P
  Q : hProp ℓ-zero
  Q = ∥ Σℕ α ∥₁ , squash₁

  openWitnessQ : isOpenWitness Q
  openWitnessQ = α , extract , ∣_∣₁

  -- ¬ Q is closed with the same witness α
  ¬Qclosed : isClosedWitness (¬ Q)
  ¬Qclosed = negOpenWitnessIsClosedWitness Q openWitnessQ

  P→¬Q : ⟨ P ⟩ → ⟨ ¬ Q ⟩
  P→¬Q p = ¬Qclosed .snd .snd (fst P↔all0 p)

  ¬Q→P : ⟨ ¬ Q ⟩ → ⟨ P ⟩
  ¬Q→P nq = snd P↔all0 (¬Qclosed .snd .fst nq)

closedWitness→negOpenWitness : (P : hProp ℓ-zero) → isClosedWitness P
  → Σ[ Q ∈ hProp ℓ-zero ] isOpenWitness Q × (⟨ P ⟩ ↔ ⟨ ¬ Q ⟩)
closedWitness→negOpenWitness P cw = Q , openWitnessQ , (P→¬Q , ¬Q→P)
  where open ClosedWitnessIsNegOpen P cw

------------------------------------------------------------------------
-- §3  Proposition level (truncated): every closed proposition is the
--     negation of an open one.
------------------------------------------------------------------------

closedIsNegationOfOpenProp : (P : hProp ℓ-zero) → isClosedProp P
  → ∥ Σ[ Q ∈ hProp ℓ-zero ] isOpenWitness Q × (⟨ P ⟩ ↔ ⟨ ¬ Q ⟩) ∥₁
closedIsNegationOfOpenProp P = PT.map (closedWitness→negOpenWitness P)

------------------------------------------------------------------------
-- §4  The easy half of de Morgan (no LLPO).
------------------------------------------------------------------------

deMorganEasy : (P Q : hProp ℓ-zero) → ⟨ ¬ P ⊔ ¬ Q ⟩ → ⟨ ¬ (P ⊓ Q) ⟩
deMorganEasy P Q disj (p , q) =
  PT.rec (snd ⊥) (⊎.rec (λ ¬p → ¬p p) (λ ¬q → ¬q q)) disj

------------------------------------------------------------------------
-- §5  Open / closed are invariant under logical equivalence, and ⊔/⊓ are
--     congruences for it.  These let us transport closedness across a ↔.
------------------------------------------------------------------------

isClosedWitness-↔ : (P R : hProp ℓ-zero) → (⟨ P ⟩ ↔ ⟨ R ⟩) → isClosedWitness R → isClosedWitness P
isClosedWitness-↔ P R (P→R , R→P) (α , R→all0 , all0→R) =
  α , (λ p → R→all0 (P→R p)) , (λ a → R→P (all0→R a))

isClosedProp-↔ : (P R : hProp ℓ-zero) → (⟨ P ⟩ ↔ ⟨ R ⟩) → isClosedProp R → isClosedProp P
isClosedProp-↔ P R e = PT.map (isClosedWitness-↔ P R e)

isOpenWitness-↔ : (P R : hProp ℓ-zero) → (⟨ P ⟩ ↔ ⟨ R ⟩) → isOpenWitness R → isOpenWitness P
isOpenWitness-↔ P R (P→R , R→P) (α , R→Σ , Σ→R) =
  α , (λ p → R→Σ (P→R p)) , (λ s → R→P (Σ→R s))

isOpenProp-↔ : (P R : hProp ℓ-zero) → (⟨ P ⟩ ↔ ⟨ R ⟩) → isOpenProp R → isOpenProp P
isOpenProp-↔ P R e = PT.map (isOpenWitness-↔ P R e)

⊔-cong↔ : (P P′ Q Q′ : hProp ℓ-zero)
  → (⟨ P ⟩ ↔ ⟨ P′ ⟩) → (⟨ Q ⟩ ↔ ⟨ Q′ ⟩) → ⟨ P ⊔ Q ⟩ ↔ ⟨ P′ ⊔ Q′ ⟩
⊔-cong↔ P P′ Q Q′ (f , f′) (g , g′) =
  PT.map (⊎.map f g) , PT.map (⊎.map f′ g′)

⊓-cong↔ : (P P′ Q Q′ : hProp ℓ-zero)
  → (⟨ P ⟩ ↔ ⟨ P′ ⟩) → (⟨ Q ⟩ ↔ ⟨ Q′ ⟩) → ⟨ P ⊓ Q ⟩ ↔ ⟨ P′ ⊓ Q′ ⟩
⊓-cong↔ P P′ Q Q′ (f , f′) (g , g′) =
    (λ pq → f (fst pq) , g (snd pq))
  , (λ pq → f′ (fst pq) , g′ (snd pq))

-- composition of logical equivalences (handy when chaining the steps above)
↔-trans : {A B C : Type} → A ↔ B → B ↔ C → A ↔ C
↔-trans (f , f′) (g , g′) = (λ a → g (f a)) , (λ c → f′ (g′ c))
