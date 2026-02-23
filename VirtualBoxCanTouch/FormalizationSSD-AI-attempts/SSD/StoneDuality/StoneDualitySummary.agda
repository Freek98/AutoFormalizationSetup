{-# OPTIONS --cubical --guardedness #-}

-- Summary of all results on the category of countably presented Boolean algebras,
-- the category of Stone spaces, and Stone duality.
--
-- This file re-exports all relevant definitions and theorems.
-- It does not contain new proofs.

module SSD.StoneDuality.StoneDualitySummary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding

open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Sigma

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Opposite

open import Cubical.HITs.PropositionalTruncation as PT

open import SSD.Library.PresentedBoole
  using ( BooleanRingEquiv
        ; has-Boole-ω'       -- tex Definition 156-159: countably presented BA
        ; has-Boole-ω        -- alternative version with explicit countability
        ; _is-presented-by_/_
        ; idBoolHom
        )

open import SSD.Library.FreeBooleanRing.FreeBool using (freeBA)
open import SSD.Library.QuotientBool as QB using (_/Im_)

open import SSD.Library.StoneDuality
  using ( -- ════════════════════════════════════════════════════════════
          -- § The type Booleω of countably presented Boolean algebras
          -- ════════════════════════════════════════════════════════════

          -- tex Definition 178: Booleω
          Booleω
          -- Booleω = Σ[ B ∈ BooleanRing ℓ-zero ] ∥ has-Boole-ω' B ∥₁

          -- ════════════════════════════════════════════════════════════
          -- § The spectrum functor Sp
          -- ════════════════════════════════════════════════════════════

          -- tex Definition 196: Sp(B) = Hom(B, 2)
        ; SpGeneralBooleanRing
          -- SpGeneralBooleanRing B = BoolHom B BoolBR
        ; Sp
          -- Sp : Booleω → Type ℓ-zero
          -- Sp = SpGeneralBooleanRing ∘ fst

        ; isSetSp
          -- Sp(B) is a set for any B

          -- ════════════════════════════════════════════════════════════
          -- § Categories BACat and BooleωCat
          -- ════════════════════════════════════════════════════════════

          -- tex line 180: Booleω has a natural category structure
        ; BACat
          -- BACat : Category (ℓ-suc ℓ-zero) ℓ-zero
          -- Objects: BooleanRing ℓ-zero
          -- Morphisms: BoolHom

        ; BooleωCat
          -- BooleωCat : Category (ℓ-suc ℓ-zero) ℓ-zero
          -- Full subcategory of BACat on countably presented BAs

        ; BACatUnivalent
          -- BACat is a univalent category
        ; BooleωUnivalent
          -- BooleωCat is a univalent category

        ; BooleωEmbedding
          -- Functor BooleωCat BACat (the inclusion)
        ; BooleωEmbeddingIsFullyFaithful
        ; BooleωEmbeddingIsEmbedding

          -- ════════════════════════════════════════════════════════════
          -- § Sp as a functor
          -- ════════════════════════════════════════════════════════════

        ; SpGeneralFunctor
          -- Functor BACat (SET ℓ-zero ^op)
        ; SpFunctor
          -- Functor BooleωCat (SET ℓ-zero ^op)
          -- SpFunctor = SpGeneralFunctor ∘F BooleωEmbedding

          -- ════════════════════════════════════════════════════════════
          -- § The 2^ functor (decidable subsets)
          -- ════════════════════════════════════════════════════════════

        ; 2^
          -- 2^ : (S : Type ℓ) → BooleanRing ℓ
          -- 2^ S = (S → Bool) with pointwise Boolean ring structure

        ; 2^Functor
          -- Functor (SET ℓ-zero ^op) BACat

          -- ════════════════════════════════════════════════════════════
          -- § The evaluation map and Stone duality axiom
          -- ════════════════════════════════════════════════════════════

        ; evaluationMapGeneralBooleanRing
          -- B → (Sp B → Bool)   for any Boolean ring B
        ; evaluationMap
          -- B → (Sp B → Bool)   for B : Booleω
        ; evaluationHomGeneralBooleanRing
          -- evaluationMap as a BoolHom B (2^ (Sp B))
        ; evaluationHom

          -- tex Axiom 285: Stone Duality
        ; StoneDualityAxiom
          -- StoneDualityAxiom = (B : Booleω) → isEquiv (evaluationMap B)
          -- States: for every B : Booleω, the evaluation map B → 2^(Sp B) is an equivalence

          -- ════════════════════════════════════════════════════════════
          -- § The adjunction Sp ⊣ 2^
          -- ════════════════════════════════════════════════════════════

        ; Sp⊣2^'
          -- SpGeneralFunctor NaturalBijection.⊣ 2^Functor
          -- The adjunction: BoolHom(B, 2^X) ≃ (X → Sp B)

        ; Sp⊣2^
          -- SpGeneralFunctor UnitCounit.⊣ 2^Functor
          -- Unit-counit form of the adjunction

        ; ηBA
          -- The unit: 𝟙⟨ BACat ⟩ ⇒ 2^Functor ∘F SpGeneralFunctor
          -- i.e. B ↦ (evaluationHom B : B → 2^(Sp B))

          -- ════════════════════════════════════════════════════════════
          -- § Stone spaces
          -- ════════════════════════════════════════════════════════════

          -- tex line 197: Stone spaces = types merely equivalent to spectra
        ; hasStoneStr
          -- hasStoneStr S = Σ[ B ∈ Booleω ] Sp B ≡ S
        ; Stone
          -- Stone = TypeWithStr ℓ-zero hasStoneStr

          -- ════════════════════════════════════════════════════════════
          -- § Results depending on the Stone duality axiom
          -- ════════════════════════════════════════════════════════════

          -- tex lines 371-392: Anti-equivalence of Booleω and Stone
        ; SpFullyFaithful
          -- (SD : StoneDualityAxiom) → isFullyFaithful SpFunctor
        ; SpEmbedding
          -- (SD : StoneDualityAxiom) → isEmbedding Sp
        ; isPropHasStoneStr
          -- (SD : StoneDualityAxiom) → (S : Set) → isProp (hasStoneStr S)
        ; SpEmbeddingIntoSets
          -- (SD : StoneDualityAxiom) → isEmbedding (SpFunctor .F-ob)

          -- ════════════════════════════════════════════════════════════
          -- § The anti-equivalence (adjunction restricted to Booleω)
          -- ════════════════════════════════════════════════════════════

        ; StoneCat
          -- (SD : StoneDualityAxiom) → Category (ℓ-suc ℓ-zero) ℓ-zero
          -- Objects: Booleω, Morphisms: maps between spectra (Sp C → Sp B)
          -- Defined as ImageFunctor.Image SpFunctor

        ; SpRestricted
          -- (SD : StoneDualityAxiom) → Functor BooleωCat StoneCat
          -- Sp restricted to its image category

        ; Sp-isEquivalence
          -- (SD : StoneDualityAxiom) → isEquivalence SpRestricted
          -- SpRestricted is fully faithful and bijective on objects,
          -- hence a categorical equivalence

        ; Sp-AntiEquivalence
          -- (SD : StoneDualityAxiom) → BooleωCat ≃ᶜ StoneCat
          -- The anti-equivalence between Booleω and Stone
        )

-- Re-export the adjunction module for detailed access
open import SSD.Library.StoneDuality
  using ( module SpDecAdjunction )
  -- SpDecAdjunction.adjunction B X : BoolHom B (2^ X) ≃ (X → Sp B)

-- Re-export the general adjunction machinery
open import SSD.Library.StoneDuality
  using ( module adjunctionFact )
  -- adjunctionFact.ηIso→FFullyFaithful :
  --   given F ⊣ G, if η is an iso at every object, then F is fully faithful
