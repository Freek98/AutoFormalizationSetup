-- Open  ↔  at-most-once-open.
--
-- A proposition is open iff it is presented by a binary sequence that hits 1 at
-- most once (i.e. an element of ℕ∞).  This is the one ingredient the LLPO de
-- Morgan argument (DisjunctionClosed) needs that is *not* yet in the library:
-- LLPO is stated for ℕ∞, so to feed it an open witness we must first replace the
-- witnessing sequence by an at-most-once one with the same ∃-hit.
--
-- The replacement itself — `onlyFirstHit`, its at-most-once-ness, and the maps
-- back and forth — now lives in the library (BinarySequences.Properties,
-- module AtMostOneHit), so this file only assembles the hProp-level statement.
-- The old §1 (firstHitOnly machinery) and §2 (Interleave.combine / fstOnEvens /
-- sndOnOdds) were *taken over* by the library rewrite (AtMostOneHit, interleave,
-- module Interleave) and have been removed.
--
-- LLPO-free.  Could be promoted to the library once the migration is committed.
module AtMostOnce where

open import BasicDefinitions using (binarySequence ; Σℕ ; _↔_ ; hits1AtMostOnce)
open import BinarySequences.Properties using (module AtMostOneHit)
open import PropositionalTopology.Definitions using (isOpenWitness ; isOpenProp)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Open  ↔  at-most-once-open.
--
-- Forward: given an open witness (α, ⟨P⟩↔Σα), pass to `onlyFirstHit α`.  It hits
-- 1 at most once (atMostOneHitInOnlyFirstHit) and has the same Σ-hit as α
-- (αToOnlyFirstHit forward, onlyFirstHitToα back).  Backward: forget the
-- at-most-once-ness.
------------------------------------------------------------------------

isAtMostOnceOpenWitness : hProp ℓ-zero → Type
isAtMostOnceOpenWitness P =
  Σ[ α ∈ binarySequence ] hits1AtMostOnce α × (⟨ P ⟩ ↔ Σℕ α)

isAtMostOnceOpenProp : hProp ℓ-zero → Type
isAtMostOnceOpenProp P = ∥ isAtMostOnceOpenWitness P ∥₁

openWitness→atMostOnceWitness : (P : hProp ℓ-zero) → isOpenWitness P → isAtMostOnceOpenWitness P
openWitness→atMostOnceWitness P (α , P→Σα , Σα→P) =
  onlyFirstHit , atMostOneHitInOnlyFirstHit ,
  ( (λ p → αToOnlyFirstHit (P→Σα p))
  , (λ (n , q) → Σα→P (n , onlyFirstHitToα n q)) )
  where open AtMostOneHit α

atMostOnceWitness→openWitness : (P : hProp ℓ-zero) → isAtMostOnceOpenWitness P → isOpenWitness P
atMostOnceWitness→openWitness P (α , _ , iso) = α , iso

openProp→atMostOnceProp : (P : hProp ℓ-zero) → isOpenProp P → isAtMostOnceOpenProp P
openProp→atMostOnceProp P = PT.map (openWitness→atMostOnceWitness P)

isOpen↔isAtMostOnceOpen : (P : hProp ℓ-zero) → isOpenProp P ↔ isAtMostOnceOpenProp P
isOpen↔isAtMostOnceOpen P =
  PT.map (openWitness→atMostOnceWitness P) , PT.map (atMostOnceWitness→openWitness P)
