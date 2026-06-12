{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
-- Continuation of FibrePresented.agda.
--
-- From the fibre construction (Sp(C/fx) ≅ fibre of Sp(f) over x) to the headline:
--   Stone duality + propositional completeness ⇒ formal surjections are surjective.
--
-- The three lemmas are BLUEPRINTED with open holes ({!!}); the surrounding structure
-- (how they compose) is filled in, so the holes have definite, type-checked goals.
module FibreConclusions where
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import Axioms.SurjectionsAreFormalSurjections

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (isoToPath)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Relation.Nullary using () renaming (¬_ to ¬ᵗ_)

open import Cubical.Algebra.CommRing 
open import Cubical.Algebra.BooleanRing 
open import Cubical.Algebra.BooleanRing.Instances.Bool 

open import BasicDefinitions 
open import BooleanRing.FreeBooleanRing.FreeBool 
open import StoneSpaces.Spectrum
  using (SpGeneralBooleanRing ; Booleω ; hasStoneStr ; StoneSpace ; Sp ; evaluationMap)
open import CountablyPresentedBooleanRings.Definitions 

open import FibrePresented

module Conclusions
  (GenB RB : Type) (GenB-count : has-Countability-structure GenB) (RB-count : has-Countability-structure RB)
  (relB : RB → ⟨ freeBA GenB ⟩)
  (GenC RC : Type) (GenC-count : has-Countability-structure GenC) (RC-count : has-Countability-structure RC)
  (relC : RC → ⟨ freeBA GenC ⟩)
  where
  open Presentation GenB RB GenB-count RB-count relB GenC RC GenC-count RC-count relC
  module _ (f : BoolHom B C) (x : SpGeneralBooleanRing B) where
    open FibersOfSp f x
    fibre : Type
    fibre = Σ[ γ ∈ SpGeneralBooleanRing C ] (γ ∘cr f ≡ x)

    C/fx-cp : is-countably-presented C/fx
    C/fx-cp = {!!}

    fibreBooleω : Booleω
    fibreBooleω = C/fx , fst (countably-presented-equivalence C/fx) C/fx-cp

    fibre-isStone : hasStoneStr fibre
    fibre-isStone = fibreBooleω , isoToPath SpC/fx≅fiber

    0≠1-in-C/fx : isInjectiveBoolHom B C f
                → ¬ᵗ (BooleanRingStr.𝟘 (snd C/fx) ≡ BooleanRingStr.𝟙 (snd C/fx))
    0≠1-in-C/fx finj 0=1 = {!  !}


      -- • x : Sp B ⇒ 0 ≠ 1 in B            (AntiEquivalence.TrivialImpliesSpEmpty)
      -- • C/fx is C cut by f(ker x): 0=1 in C/fx ⇒ 1 ∈ ⟨f(ker x)⟩ ⇒ f k ≡ 1 ≡ f 𝟙 for some
      --   k ∈ ker x.  f injective (kernel = {𝟘}) ⇒ k ≡ 𝟙_B ; but x k ≡ 0 (k ∈ ker x) ≠ 1 ≡ x 𝟙_B.  ⊥.
      --   (ker≡0→injBoolHom = the kernel/injectivity form, in SurjectionsAreFormalSurjections.)

    ----------------------------------------------------------------
    -- (3)  with Stone duality (SD) and propositional completeness (PC):
    --      the fibre over x is (merely) inhabited — i.e. Sp(f) hits x.
    ----------------------------------------------------------------
    module conclusion
      (SD   : (D : Booleω) → isEquiv (evaluationMap D))
      (PC   : (S : StoneSpace) → ¬ᵗ ¬ᵗ ⟨ S ⟩ → ∥ ⟨ S ⟩ ∥₁)
      (finj : (b b' : ⟨ B ⟩) → f $cr b ≡ f $cr b' → b ≡ b')
      where
      ¬¬fibre : ¬ᵗ ¬ᵗ fibre
      ¬¬fibre = {!!}
        -- ¬ fibre ⇒ ¬ Sp(C/fx)  (transport along SpC/fx≅fiber)
        --        ⇒ 0=1 in C/fx   (AntiEquivalence.SpectrumEmptyImpliesTrivial SD fibreBooleω)
        --        ⇒ ⊥             (0≠1-in-C/fx finj).

      -- propositional completeness turns ¬¬ into mere existence:
      fibre-inhabited : ∥ fibre ∥₁
      fibre-inhabited = PC (fibre , fibre-isStone) ¬¬fibre
      -- quantifying fibre-inhabited over all x : Sp B is exactly surjectivity of Sp(f),
      -- i.e. "formal surjections are surjective".
