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
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Bool 
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing using (_$cr_ ; _∘cr_)
open import Cubical.Algebra.BooleanRing using (BooleanRing ; BoolHom)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)

open import BasicDefinitions 
open import BooleanRing.FreeBooleanRing.FreeBool 
open import StoneSpaces.Spectrum
open import BooleanRing.BooleanRingQuotients.UniversalProperty
open import Cubical.Foundations.Isomorphism
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
  (GenC RC : Type)
  (GenC-count : has-Countability-structure GenC)
  (RC-count   : has-Countability-structure RC)
  (relC : RC → ⟨ freeBA GenC ⟩)
  where

  B : BooleanRing ℓ-zero
  B = freeBA GenB /Im relB

  -- the quotient map  freeBA GenB ↠ B  (so the generators of B are πB (generator g))
  πB : BoolHom (freeBA GenB) B
  πB = quotientImageHom {B = freeBA GenB} {f = relB}

  -- … and C, presented the same way.
  C : BooleanRing ℓ-zero
  C = freeBA GenC /Im relC

  πC : BoolHom (freeBA GenC) C
  πC = quotientImageHom {B = freeBA GenC} {f = relC}

  -- a point x : Sp B, read off on the generators of B

  _$gen_ : (SpGeneralBooleanRing B) → GenB → Bool
  x $gen g = (x ∘cr πB) $cr generator g 
  module generatorsSentTo0 (x : BoolHom B BoolBR) where
    GenB0 : Type
    GenB0 = Σ[ g ∈ GenB ] (not (x $gen g) ≡ true)

    GenB0-count : has-Countability-structure GenB0
    GenB0-count = has-Countability-structure-Σ-Bool (not ∘ (x $gen_)) GenB-count

    -- Given f : B → C, quotient C by the f-images of the x-zero generators.
    module overMap (f : BoolHom B C) where
      -- relations:  f(genB g)  for each generator g sent to 0 by x
      relD0 : GenB0 → ⟨ C ⟩
      relD0 (g , _) = (f ∘cr πB) $cr generator g        -- = f (genB g)

      D0 : BooleanRing ℓ-zero
      D0 = C /Im relD0

      -- Sp(D0) ≅ the points h : C → 2 whose pullback h∘f kills every x-zero generator,
      -- i.e. (h∘f)(g) = 0 for every generator g with x(g) = 0.
      --
      -- NB this is the "sent-to-0 half" of the fibre over x: it imposes (h∘f)(g)=0 where
      -- x(g)=0, but not (h∘f)(g)=1 where x(g)=1.  Adding the complementary relations
      -- (f(genB g)+1 for the x-one generators) cuts Sp down to the full fibre {h ∣ h∘f = x}.
      SpD0≅ : Iso (SpGeneralBooleanRing D0)
                  (Σ[ h ∈ SpGeneralBooleanRing C ] ((p : GenB0) → (h ∘cr f) $gen (fst p) ≡ false))
      SpD0≅ = invIso (MapsOutOfQuotientUniversalProperty.mapsOutQuotientUniversalProperty C relD0 BoolBR)
