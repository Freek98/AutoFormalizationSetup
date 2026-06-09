{-# OPTIONS --lossy-unification #-}
-- Step-by-step construction of the fibre Stone space, built from explicit
-- presentations.  This file starts the development from the presentation of B and
-- records the two foundational facts requested:
--
--   §1  for x : Sp B, the subset  { g ∈ GenB ∣ x(g) = 1 }  of the generators is
--       decidable (its membership is x(g) ≟ true, a decidable equality of Bool);
--   §2  a decidable subset of a countable set is again countable
--       (general lemma `has-Countability-structure-decΣ`, built on the library's
--        Bool-predicate version `has-Countability-structure-Σ-Bool`), and hence the
--       subset of step §1 is countable.
--
-- Later steps (C's presentation, the fibre algebra Dₓ as a quotient of C, and
-- Sp(Dₓ) ≅ fibre) build on this.  The Sp(Dₓ) ≅ fibre half is already in
-- FiberStoneSpace.agda; here we rebuild the countability/presentation side cleanly.
module FibrePresented where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool using (Bool ; true ; false ; _≟_ ; false≢true ; isSetBool)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (Dec ; yes ; no)

open import Cubical.Algebra.CommRing using (_$cr_ ; _∘cr_)
open import Cubical.Algebra.BooleanRing using (BooleanRing ; BoolHom)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)

open import BasicDefinitions using (has-Countability-structure)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA ; generator)
open import BooleanRing.BooleanRingQuotients.QuotientBool using (_/Im_ ; quotientImageHom)
open import Countability.Properties using (has-Countability-structure-Σ-Bool ; has-Countability-structure-Iso)

------------------------------------------------------------------------
-- A decidable subset of a countable set is countable.
--
-- The library already proves this for subsets presented by a Bool characteristic
-- function (has-Countability-structure-Σ-Bool).  A decidable subset — a prop-valued
-- predicate P with decidable membership — is the same data: turn `dec` into the
-- characteristic function `decToBool ∘ dec` and transport along the (pointwise) iso
-- `P a ≅ (decToBool (dec a) ≡ true)`.
------------------------------------------------------------------------

decToBool : {ℓ : Level} {P : Type ℓ} → Dec P → Bool
decToBool (yes _) = true
decToBool (no  _) = false

-- a decidable proposition is the "= true" fibre of its Bool decision
decToBool-iso : {ℓ : Level} {P : Type ℓ} → isProp P → (d : Dec P) → Iso P (decToBool d ≡ true)
decToBool-iso pr (yes p) = isProp→Iso pr (isSetBool _ _) (λ _ → refl)            (λ _ → p)
decToBool-iso pr (no ¬p) = isProp→Iso pr (isSetBool _ _) (λ p → ⊥.rec (¬p p))    (λ q → ⊥.rec (false≢true q))

has-Countability-structure-decΣ : {A : Type} (P : A → Type)
  → ((a : A) → isProp (P a)) → ((a : A) → Dec (P a))
  → has-Countability-structure A → has-Countability-structure (Σ[ a ∈ A ] P a)
has-Countability-structure-decΣ P prop dec cA =
  has-Countability-structure-Iso
    (has-Countability-structure-Σ-Bool (λ a → decToBool (dec a)) cA)
    (Σ-cong-iso-snd (λ a → invIso (decToBool-iso (prop a) (dec a))))

------------------------------------------------------------------------
-- B given by a presentation:  generators GenB, relations RB / relB.
------------------------------------------------------------------------

module Presentation
  (GenB RB : Type)
  (GenB-count : has-Countability-structure GenB)
  (RB-count   : has-Countability-structure RB)
  (relB : RB → ⟨ freeBA GenB ⟩)
  where

  B : BooleanRing ℓ-zero
  B = freeBA GenB /Im relB

  -- the quotient map  freeBA GenB ↠ B  (so the generators of B are πB (generator g))
  πB : BoolHom (freeBA GenB) B
  πB = quotientImageHom {B = freeBA GenB} {f = relB}

  -- a point x : Sp B, read off on the generators of B
  module _ (x : BoolHom B BoolBR) where

    xOnGen : GenB → Bool
    xOnGen g = (x ∘cr πB) $cr generator g

    ----------------------------------------------------------------
    -- §1  Membership of the subset { g ∣ x(g) = 1 } is decidable.
    ----------------------------------------------------------------
    GenB₁-dec : (g : GenB) → Dec (xOnGen g ≡ true)
    GenB₁-dec g = (xOnGen g) ≟ true

    -- the subset itself
    GenB₁ : Type
    GenB₁ = Σ[ g ∈ GenB ] (xOnGen g ≡ true)

    ----------------------------------------------------------------
    -- §2  It is countable (decidable subset of a countable set).
    ----------------------------------------------------------------
    GenB₁-count : has-Countability-structure GenB₁
    GenB₁-count = has-Countability-structure-decΣ
                    (λ g → xOnGen g ≡ true)
                    (λ g → isSetBool _ _)
                    GenB₁-dec
                    GenB-count

    -- (equivalently, directly via the Bool characteristic function xOnGen:)
    GenB₁-count' : has-Countability-structure GenB₁
    GenB₁-count' = has-Countability-structure-Σ-Bool xOnGen GenB-count
