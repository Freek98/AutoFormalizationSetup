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
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.HLevels using (isPropΠ)
import Cubical.Data.Empty as ⊥

open import Cubical.Data.Bool 
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import BasicDefinitions
open import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.BoolAlgMorphism using (module IsBoolAlgHom)
open import CountablyPresentedBooleanRings.Properties
open import StoneSpaces.Spectrum
open import BooleanRing.BooleanRingQuotients.UniversalProperty
open import Cubical.Foundations.Isomorphism
open import BooleanRing.BooleanRingQuotients.QuotientBool

------------------------------------------------------------------------
-- A Bool fact used per generator.
------------------------------------------------------------------------
private
  not≡false→≡true : (c : Bool) → not c ≡ false → c ≡ true
  not≡false→≡true true  _ = refl
  not≡false→≡true false p = ⊥.rec (true≢false p)

  Σ-cong-iso-prop : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {P : A → Type ℓ'} {Q : A → Type ℓ''}
                  → (∀ a → isProp (P a)) → (∀ a → isProp (Q a))
                  → (∀ a → P a → Q a) → (∀ a → Q a → P a) → Iso (Σ A P) (Σ A Q)
  Σ-cong-iso-prop pP pQ to fro = Σ-cong-iso-snd (λ a → isProp→Iso (pP a) (pQ a) (to a) (fro a))

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

  C : BooleanRing ℓ-zero
  C = freeBA GenC /Im relC

  private
    πB : BoolHom (freeBA GenB) B
    πB = quotientImageHom {B = freeBA GenB} {f = relB}

    πC : BoolHom (freeBA GenC) C
    πC = quotientImageHom {B = freeBA GenC} {f = relC}
  
  open RepresentedBooleanRing relB 

  module FibersOfSp (f : BoolHom B C) (x : SpGeneralBooleanRing B) where
    open BooleanAlgebraStr (snd C) using (¬_)

    if_thenPos_ : Bool → ⟨ C ⟩ → ⟨ C ⟩
    if_thenPos_ false c = c
    if_thenPos_ true  c = ¬ c

    relInducedByfandx : GenB → ⟨ C ⟩
    relInducedByfandx g = if (x $gen g) thenPos ((f ∘cr πB) $cr generator g) 
    
    C/fx : BooleanRing ℓ-zero 
    C/fx = C /Im relInducedByfandx

    respRel→agree : (γ : SpGeneralBooleanRing C) (g : GenB)
                → γ $cr relInducedByfandx g ≡ false → (γ ∘cr f) $gen g ≡ x $gen g
    respRel→agree γ g = aux (x $gen g)
      where
        fg = f $gen g 
        aux : (b : Bool) → γ $cr (if b thenPos fg) ≡ false → γ $cr fg ≡ b
        aux false p = p
        aux true  p = not≡false→≡true (γ $cr fg) (sym (IsBoolAlgHom.pres¬ γ fg) ∙ p)

    agree→respRel : (γ : SpGeneralBooleanRing C) (g : GenB)
                  → (γ ∘cr f) $gen g ≡ x $gen g → γ $cr relInducedByfandx g ≡ false
    agree→respRel γ g = aux (x $gen g)
      where
        fg = f $gen g 
        aux : (b : Bool) → γ $cr fg ≡ b → γ $cr (if b thenPos fg) ≡ false
        aux false p = p
        aux true  p = IsBoolAlgHom.pres¬ γ fg ∙ cong not p

    private
      Σγ-γRespRel : Type
      Σγ-γRespRel = Σ[ γ ∈ SpGeneralBooleanRing C ] ((g : GenB) → γ $cr relInducedByfandx g ≡ false)
      Σγ-γf=x-OnG : Type 
      Σγ-γf=x-OnG = Σ[ γ ∈ SpGeneralBooleanRing C ] ((g : GenB) → (γ ∘cr f) $gen g ≡ x $gen g)
      
    fiberSpf : Type 
    fiberSpf = Σ[ γ ∈ SpGeneralBooleanRing C ] (γ ∘cr f) ≡ x

    UP-C/fx : Iso Σγ-γRespRel (SpGeneralBooleanRing C/fx)
    UP-C/fx = MapsOutOfQuotientUniversalProperty.mapsOutQuotientUniversalProperty C relInducedByfandx BoolBR

    respRel↔agreeOnG : Iso Σγ-γRespRel Σγ-γf=x-OnG
    respRel↔agreeOnG = Σ-cong-iso-prop
      (λ _ → isPropΠ (λ g → isSetBool _ _)) (λ _ → isPropΠ (λ g → isSetBool _ _))
      (λ γ resp g → respRel→agree γ g (resp g))
      (λ γ agr  g → agree→respRel γ g (agr g))

    agreeOnG↔f=x : Iso Σγ-γf=x-OnG fiberSpf
    agreeOnG↔f=x = Σ-cong-iso-prop
      (λ _ → isPropΠ (λ g → isSetBool _ _)) (λ γ → isSetBoolHom B BoolBR (γ ∘cr f) x)
      (λ γ → agreeOnGens≡ BoolBR)
      (λ γ eq g → cong (λ h → h $gen g) eq)

    SpC/fx≅fiber : Iso (SpGeneralBooleanRing C/fx) fiberSpf
    SpC/fx≅fiber = compIso (compIso (invIso UP-C/fx) respRel↔agreeOnG) agreeOnG↔f=x

