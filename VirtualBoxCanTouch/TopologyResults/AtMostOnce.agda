-- Reusable binary-sequence infrastructure for the propositional-topology development.
--
-- Two independent constructions on binary sequences, plus the characterisation of
-- open propositions they enable:
--
--   * firstHitOnly α   : keep only the first 1 of α.  It has the *same* ∃-hit as α
--                        but hits 1 at most once (it lives in ℕ∞).
--   * Interleave.combine α β : the sequence that is α on the evens and β on the odds.
--   * isOpen ↔ isAtMostOnceOpen : every open proposition is presented by an
--                        at-most-once sequence (apply firstHitOnly to any witness).
--
-- This file is LLPO-free.  It used to live inline in DisjunctionClosed; it is kept here
-- in the project (rather than the shared FormalizationSSD library, which is synced via
-- git) and could be promoted to the library once that migration is committed.
module AtMostOnce where

open import BasicDefinitions                       -- binarySequence, Σℕ, _↔_, hits1AtMostOnce
open import BinarySequences using (and-true→×)
open import BinarySequences.Properties 
open import PropositionalTopology.Definitions      -- isOpenWitness , isOpenProp

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; doubleℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; true≢false ; false≢true)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)
import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁ ; squash₁)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- §1  firstHitOnly: turn any sequence into an at-most-once one with the
--     same ∃-hit.
------------------------------------------------------------------------

-- noHitBefore α n  ≡ true  iff  α is 0 on every k < n.
open AtMostOneHit

not≡true→≡false : (b : Bool) → not b ≡ true → b ≡ false
not≡true→≡false false _ = refl
not≡true→≡false true  p = Empty.rec (false≢true p)

noHitBefore-spec : (α : binarySequence) (n : ℕ)
  → noHitBefore α n ≡ true → (k : ℕ) → k < n → α k ≡ false
noHitBefore-spec α zero    p k k<0  = Empty.rec (¬-<-zero k<0)
noHitBefore-spec α (suc n) p k k<sn with and-true→× (noHitBefore α n) (not (α n)) p | <-split k<sn
... | (nhb , _)   | inl k<n = noHitBefore-spec α n nhb k k<n
... | (_ , notαn) | inr k≡n = subst (λ j → α j ≡ false) (sym k≡n) (not≡true→≡false (α n) notαn)

allFalseBefore→noHitBefore : (α : binarySequence) (n : ℕ)
  → ((k : ℕ) → k < n → α k ≡ false) → noHitBefore α n ≡ true
allFalseBefore→noHitBefore α zero    _        = refl
allFalseBefore→noHitBefore α (suc n) allFalse =
  cong₂ _and_
    (allFalseBefore→noHitBefore α n (λ k k<n → allFalse k (≤-suc k<n)))
    (cong not (allFalse n ≤-refl))

firstHitOnly→hit : (α : binarySequence) (n : ℕ) → firstHitOnly α n ≡ true → α n ≡ true
firstHitOnly→hit α n p = fst (and-true→× (α n) (noHitBefore α n) p)

-- uniqueness of the first hit (firstProp) gives at-most-once for free
firstHitOnlyAtMostOnce : (α : binarySequence) → hits1AtMostOnce (firstHitOnly α)
firstHitOnlyAtMostOnce α n m fn fm =
  cong fst (isPropFirstHit (n , toFirst n fn) (m , toFirst m fm))
  where
    open AtMostOneHit α
    toFirst : (k : ℕ) → firstHitOnly α k ≡ true → firstHitAt k
    toFirst k fk = firstHitOnly→hit α k fk
                 , noHitBefore-spec α k (snd (and-true→× (α k) (noHitBefore α k) fk))

-- same ∃-hit as α (forward uses extractFirst to land on the first hit)
Σα↔ΣfirstHitOnly : (α : binarySequence) → Σℕ α ↔ Σℕ (firstHitOnly α)
Σα↔ΣfirstHitOnly α = fwd , bwd
  where
    open extractFirstHitInBinarySequence α
    fwd : Σℕ α → Σℕ (firstHitOnly α)
    fwd (n , αn) =
      fst fh , cong₂ _and_ (fst (snd fh))
                           (allFalseBefore→noHitBefore α (fst fh) (snd (snd fh)))
      where fh = extractFirst ∣ (n , αn) ∣₁
    bwd : Σℕ (firstHitOnly α) → Σℕ α
    bwd (n , p) = n , firstHitOnly→hit α n p

------------------------------------------------------------------------
-- §2  Interleave two sequences: α on the evens, β on the odds.
------------------------------------------------------------------------

tail : binarySequence → binarySequence
tail α n = α (suc n)

module Interleave where
  combine : binarySequence → binarySequence → binarySequence
  combine α β zero          = α zero
  combine α β (suc zero)    = β zero
  combine α β (suc (suc n)) = combine (tail α) (tail β) n

  fstOnEvens : (α β : binarySequence) (k : ℕ) → combine α β (doubleℕ k) ≡ α k
  fstOnEvens α β zero    = refl
  fstOnEvens α β (suc k) = fstOnEvens (tail α) (tail β) k

  sndOnOdds : (α β : binarySequence) (k : ℕ) → combine α β (suc (doubleℕ k)) ≡ β k
  sndOnOdds α β zero    = refl
  sndOnOdds α β (suc k) = sndOnOdds (tail α) (tail β) k

  -- a hit of the interleaving at an even / odd index comes from a hit of α / β
  evenHit : (α β : binarySequence) (n a : ℕ) → n ≡ doubleℕ a → combine α β n ≡ true → α a ≡ true
  evenHit α β n a n≡2a hit = sym (fstOnEvens α β a) ∙ cong (combine α β) (sym n≡2a) ∙ hit

  oddHit : (α β : binarySequence) (n a : ℕ) → n ≡ suc (doubleℕ a) → combine α β n ≡ true → β a ≡ true
  oddHit α β n a n≡2a+1 hit = sym (sndOnOdds α β a) ∙ cong (combine α β) (sym n≡2a+1) ∙ hit

------------------------------------------------------------------------
-- §3  Open  ↔  at-most-once-open.
--
-- A proposition is open iff it is presented by a sequence that hits 1 at
-- most once (i.e. an element of ℕ∞).  Forward: apply firstHitOnly to any
-- open witness.  Backward: forget the at-most-once-ness.
------------------------------------------------------------------------

isAtMostOnceOpenWitness : hProp ℓ-zero → Type
isAtMostOnceOpenWitness P =
  Σ[ α ∈ binarySequence ] hits1AtMostOnce α × (⟨ P ⟩ ↔ Σℕ α)

isAtMostOnceOpenProp : hProp ℓ-zero → Type
isAtMostOnceOpenProp P = ∥ isAtMostOnceOpenWitness P ∥₁

openWitness→atMostOnceWitness : (P : hProp ℓ-zero) → isOpenWitness P → isAtMostOnceOpenWitness P
openWitness→atMostOnceWitness P (α , P→Σα , Σα→P) =
  firstHitOnly α , firstHitOnlyAtMostOnce α ,
  ( (λ p → fst (Σα↔ΣfirstHitOnly α) (P→Σα p))
  , (λ s → Σα→P (snd (Σα↔ΣfirstHitOnly α) s)) )

atMostOnceWitness→openWitness : (P : hProp ℓ-zero) → isAtMostOnceOpenWitness P → isOpenWitness P
atMostOnceWitness→openWitness P (α , _ , iso) = α , iso

openProp→atMostOnceProp : (P : hProp ℓ-zero) → isOpenProp P → isAtMostOnceOpenProp P
openProp→atMostOnceProp P = PT.map (openWitness→atMostOnceWitness P)

isOpen↔isAtMostOnceOpen : (P : hProp ℓ-zero) → isOpenProp P ↔ isAtMostOnceOpenProp P
isOpen↔isAtMostOnceOpen P =
  PT.map (openWitness→atMostOnceWitness P) , PT.map (atMostOnceWitness→openWitness P)
