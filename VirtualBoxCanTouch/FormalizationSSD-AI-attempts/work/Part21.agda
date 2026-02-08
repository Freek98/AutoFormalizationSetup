{-# OPTIONS --cubical --guardedness #-}
-- Note from Freek, after cleaning up, only postulates remained. I guess the phrasing of the postulates could have some value as stating the future proof goals. 
module work.Part21 where

open import work.Part20 public

module StoneSeparatedTC where
  open import Axioms.StoneDuality using (Stone)
  open StoneSeparatedModule

  -- TEX LEMMA 1824 - StoneSeparated
  -- STATEMENT (tex lines 1824-1827):
  -- PROOF SKETCH (tex lines 1828-1858):

  StoneSeparated-postulate : (S : Stone)
    → (F G : ClosedSubsetOfStone S)
    → ClosedSubsetsDisjoint S F G
    → ∥ Σ[ D ∈ DecSubsetOfStone S ] (ClosedSubDec S F D) × (ClosedSubNotDec S G D) ∥₁
  StoneSeparated-postulate = StoneSeparated

  open StoneSeparatedModule public using
    ( ClosedSubsetOfStone
    ; DecSubsetOfStone
    ; ClosedSubsetsDisjoint
    ; ClosedSubDec
    ; ClosedSubNotDec
    ; closedComplementIsOpen
    )

-- CHausFiniteIntersectionPropertyTC (tex Lemma 1981)
-- This module documents tex Lemma 1981: Compact Hausdorff spaces have the

module CHausFiniteIntersectionPropertyTC where
  open CompactHausdorffModule using (CHaus)
  open CHausFiniteIntersectionPropertyModule

  -- TEX LEMMA 1981 - CHausFiniteIntersectionProperty
  -- STATEMENT (tex lines 1981-1984):
  -- PROOF SKETCH (tex lines 1985-2001):

  CHausFiniteIntersectionProperty-postulate : (X : CHaus)
    → (C : ℕ → fst X → hProp ℓ-zero)
    → ((n : ℕ) (x : fst X) → isClosedProp (C n x))
    → ((x : fst X) → ((n : ℕ) → fst (C n x)) → ⊥)
    → ∥ Σ[ k ∈ ℕ ] ((x : fst X) → ¬ fst (finiteIntersectionClosed C k x)) ∥₁
  CHausFiniteIntersectionProperty-postulate = CHausFiniteIntersectionProperty

-- CHausSeperationOfClosedByOpensTC (tex Lemma 2058)
-- This module documents tex Lemma 2058: Compact Hausdorff spaces are normal.

module CHausSeperationOfClosedByOpensTC where
  open CompactHausdorffModule using (CHaus)
  open CHausSeperationOfClosedByOpensModule

  -- TEX LEMMA 2058 - CHausSeperationOfClosedByOpens
  -- STATEMENT (tex lines 2058-2061):
  -- PROOF SKETCH (tex lines 2062-2076):
  -- 3. By StoneSeperated (tex 1824), there exists D : S → 2 such that:
  -- - StoneSeparated (tex 1824): POSTULATED

  CHausSeperationOfClosedByOpens-postulate :
    (X : CHaus)
    → (A B : fst X → hProp ℓ-zero)
    → ((x : fst X) → isClosedProp (A x))
    → ((x : fst X) → isClosedProp (B x))
    → areDisjoint A B
    → ∥ Σ[ U ∈ (fst X → hProp ℓ-zero) ] Σ[ V ∈ (fst X → hProp ℓ-zero) ]
        ((x : fst X) → isOpenProp (U x)) ×
        ((x : fst X) → isOpenProp (V x)) ×
        subsetOf A U × subsetOf B V × areDisjoint U V ∥₁
  CHausSeperationOfClosedByOpens-postulate = CHausSeperationOfClosedByOpens

module StonePropertiesTC where
  open import Axioms.StoneDuality using (Stone)

  -- TEX LEMMA 251 - ClosedPropAsSpectrum

  -- TEX LEMMA 1636 - StoneEqualityClosed
  -- PROOF SKETCH (from tex):

  -- TEX COROLLARY 1628 - PropositionsClosedIffStone

  -- TEX COROLLARY 1613 - TruncationStoneClosed

  -- TEX LEMMA 1770/1776 - ClosedInStoneIsStone
  -- PROOF SKETCH (from tex):

  -- TEX LEMMA 1906 - CompactHausdorffClosed

  -- TEX COROLLARY 1930 - InhabitedClosedSubSpaceClosedCHaus

  -- 1. ClosedPropAsSpectrum (tex 251)
  -- 2. PropositionsClosedIffStone (tex 1628)
  -- 3. StoneEqualityClosed (tex 1636)
  -- 4. ClosedInStoneIsStone (tex 1770)
  -- 5. CompactHausdorffClosed (tex 1906)
  -- 6. InhabitedClosedSubSpaceClosedCHaus (tex 1930)
  -- 7. IVT, BFT (tex 3082, 3099)

module CHausStructuralTC where
  open CompactHausdorffModule using (CHaus; hasCHausStr)

  -- TEX COROLLARY 2003 - ChausMapsPreserveIntersectionOfClosed

  -- TEX COROLLARY 2019 - CompactHausdorffTopology

  -- TEX LEMMA 2098 - SigmaCompactHausdorff

  -- The tex proves CHaus is closed under many operations:
  -- 2. Σ-types (tex 2098, SigmaCompactHausdorff)

-- This module documents the 5 foundational axioms from the tex file that
