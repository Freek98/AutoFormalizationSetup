{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
-- Exploration (open question): does LLPO imply propositional completeness?
--
-- Propositional completeness, PC:
--     (S : StoneSpace) → ¬¬ ⟨ S ⟩ → ∥ ⟨ S ⟩ ∥₁
-- i.e. for a Stone space S = Sp D (D countably presented), "S is ¬¬-inhabited" ⇒ "S is
-- merely inhabited".
--
-- LLPO:
--     (x : ℕ∞) → ∥ (∀ n, x(2n)=0) ⊎ (∀ n, x(2n+1)=0) ∥₁
-- (for a binary sequence hitting 1 at most once, the evens are all 0 or the odds are all 0).
--
-- ANALYSIS.  A point of Sp D is a hom D → 2.  Writing D = freeBA ℕ /Im r (r : ℕ → freeBA ℕ
-- the relations), a point is a binary sequence α : ℕ → Bool on the generators that *respects*
-- every relation (eval α (r n) ≡ 0 for all n).  These respecting conditions are decidable, so
--      Sp D  ≅  { α ∈ 2^ℕ ∣ ∀ n, decidable-condition n α }
-- is a *closed* subspace of Cantor space.  So PC says exactly:
--      every ¬¬-inhabited closed subset of Cantor space is (merely) inhabited.
-- That is a compactness / weak-König-flavoured principle: to actually produce a point you build
-- a branch generator-by-generator, at each step keeping the partial assignment ¬¬-extendable —
-- a Σ⁰₁-strength choice at every node.  In constructive reverse mathematics this is WKL-flavoured
-- and is **strictly stronger than LLPO** (WKL ⇒ LLPO, not conversely).  So LLPO → PC is *not*
-- expected to hold, and the hole below is where that gap sits: LLPO only resolves a single
-- "evens-or-odds" dichotomy, not the ω-many consistent choices a branch needs.
--
-- (Consistent with the rest of the development: PC is what one gets from StoneDuality +
--  formalSurjections — both non-constructive — via Axioms.Axiom2.)
--
-- This file states the implication and leaves it as an open hole with the obstruction noted;
-- a fragment that LLPO *does* give is the single-dichotomy case (ℕ∞-shaped spaces).
--
-- ADD DEPENDENT CHOICE and it goes through: DC + LLPO → WKL → PC.  LLPO supplies the per-node
-- "left-or-right subtree infinite" dichotomy and DC assembles a coherent branch.  That route is
-- formalised (as a skeleton with the bookkeeping holes) in WKLfromDCLLPO.agda.
module LLPOtoPC where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Relation.Nullary using () renaming (¬_ to ¬ᵗ_)

open import StoneSpaces.Spectrum using (StoneSpace)
open import OmnisciencePrinciples.LLPO using (LLPO)

PropositionalCompleteness : Type _
PropositionalCompleteness = (S : StoneSpace) → ¬ᵗ ¬ᵗ ⟨ S ⟩ → ∥ ⟨ S ⟩ ∥₁

-- The implication under question.  Conjecturally NOT provable (PC is WKL-strength); the hole
-- marks the ω-many consistent branch-choices that a single LLPO dichotomy cannot supply.
LLPO→PC : LLPO → PropositionalCompleteness
LLPO→PC llpo S ¬¬S = {!!}
