{-# OPTIONS --lossy-unification #-}
-- Step-by-step construction of the fibre Stone space, built from explicit
-- presentations.  A "subset" of a set here means a characteristic function into Bool;
-- its members are the points sent to `true`.
--
--   §1  for x : Sp B, the subset { g ∈ GenB ∣ x(g) = 1 } of the generators is the
--       characteristic function  xOnGen g = (x ∘cr πB)(generator g) : GenB → Bool;
--   §2  a Bool-subset of a countable set is countable
--       (library: has-Countability-structure-Σ-Bool), so this subset is countable.
--
-- Later steps (C's presentation, the fibre algebra Dₓ as a quotient of C, and
-- Sp(Dₓ) ≅ fibre — the last already in FiberStoneSpace.agda) build on this.
module FibrePresented where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Bool using (Bool ; true)
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing using (_$cr_ ; _∘cr_)
open import Cubical.Algebra.BooleanRing using (BooleanRing ; BoolHom)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)

open import BasicDefinitions 
open import BooleanRing.FreeBooleanRing.FreeBool 
open import StoneSpaces.Spectrum
open import BooleanRing.BooleanRingQuotients.QuotientBool 
open import Countability.Properties 

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

  _$gen_ : (SpGeneralBooleanRing B) → GenB → Bool
  x $gen g = (x ∘cr πB) $cr generator g 
  module generatorsSentTo1 (x : BoolHom B BoolBR) where
    GenB₁ : Type
    GenB₁ = Σ[ g ∈ GenB ] (x $gen g ≡ true)

    GenB₁-count : has-Countability-structure GenB₁
    GenB₁-count = has-Countability-structure-Σ-Bool (x $gen_) GenB-count
