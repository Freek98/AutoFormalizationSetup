-- Companion to the AtMostOneHit refactor in BinarySequences.Properties (commit
-- 8cab29a "Have refactored the decidable property into a binary sequence").
--
-- This file now *imports* your library module and only adds the pieces that finish
-- the refactor, all phrased in your current names (noHitBefore, onlyFirstHit,
-- onlyFirstHitToα, onlyFirstHitToNoEarlierHit, atMostOneHitInOnlyFirstHit, firstHitAt,
-- ℕ∞SequenceProperties.splitSupportΣℕ1):
--
--   §0  allFalseBefore→noHitBefore   the converse of noHitBefore→SoFarAll0
--   §1  firstHitAt ↔ onlyFirstHit≡true   ← the function you asked for
--   §2  αToFirstHit + extract         the onlyFirstHit-based `extract`, replacing the
--                                     decidableFirst / firstSeenBefore machinery
module ExtractRefactorProposal where

open import BinarySequences.Definitions        -- binarySequence , Σℕ1 , hits1AtMostOnce
open import BinarySequences.Properties          -- AtMostOneHit , ℕ∞SequenceProperties
open import BasicDefinitions using (_↔_)        -- A ↔ B = (A → B) × (B → A)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; case_of_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order
  using (_<_ ; ¬-<-zero ; ≤-refl ; ≤-suc ; ≤-trans ; pred-≤-pred)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; _and_
        ; true≢false ; ¬true→false) renaming (_≟_ to _=B_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Relation.Nullary using (yes ; no)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)

module _ (α : binarySequence) where
  open AtMostOneHit α

  ----------------------------------------------------------------------
  -- §0  Converse of your noHitBefore→SoFarAll0.
  --     (Uses only the defining equations of noHitBefore.)
  ----------------------------------------------------------------------

  onlyFirstHit→firstHitAt : (n : ℕ) → onlyFirstHit n ≡ true → firstHitAt n
  onlyFirstHit→firstHitAt n p = onlyFirstHitToα n p , onlyFirstHitToNoEarlierHit n p

  firstHitAt→onlyFirstHit : (n : ℕ) → firstHitAt n → onlyFirstHit n ≡ true
  firstHitAt→onlyFirstHit n (αn , noBefore) =
    cong₂ _and_ αn (allFalseBefore→noHitBefore n noBefore)

  firstHitAt↔onlyFirstHit : (n : ℕ) → firstHitAt n ↔ (onlyFirstHit n ≡ true)
  firstHitAt↔onlyFirstHit n = firstHitAt→onlyFirstHit n , onlyFirstHit→firstHitAt n

  ----------------------------------------------------------------------
  -- §2  The onlyFirstHit-based `extract`, for comparison with the decidable one.
  --
  --   αToFirstHit is the only search, and it is structural on a fuel argument
  --   (the witness index is an explicit bound) — no decidableFirst.  Then your
  --   ℕ∞SequenceProperties.splitSupportΣℕ1 does the rest, because onlyFirstHit
  --   hits at most once (atMostOneHitInOnlyFirstHit).
  ----------------------------------------------------------------------
  private
    deMorganBool : (a b : Bool) → a and b ≡ false → (a ≡ false) ⊎ (b ≡ false)
    deMorganBool false _ _ = inl refl
    deMorganBool true  b p = inr p

    not≡false→≡true : (b : Bool) → not b ≡ false → b ≡ true
    not≡false→≡true false p = ex-falso (true≢false p)
    not≡false→≡true true  _ = refl

    -- noHitBefore n ≡ false already exhibits an earlier hit (with its bound).

  αToFirstHit : Σℕ1 α → Σℕ1 onlyFirstHit
  αToFirstHit (n , αn) = findFirstAux (suc n) n ≤-refl αn

  extractViaOnlyFirstHit : ∥ Σℕ1 α ∥₁ → Σℕ1 α
  extractViaOnlyFirstHit =
            forget
          ∘ ℕ∞SequenceProperties.splitSupportΣℕ1 onlyFirstHit atMostOneHitInOnlyFirstHit
          ∘ PT.map αToFirstHit
    where
      forget : Σℕ1 onlyFirstHit → Σℕ1 α
      forget (n , p) = n , onlyFirstHitToα n p
