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
open import Cubical.Foundations.HLevels using (isPropΠ)
import Cubical.Data.Empty as ⊥

open import Cubical.Data.Bool 
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing using (_$cr_ ; _∘cr_ ; CommRingHom≡ ; IsCommRingHom)
open import Cubical.Algebra.BooleanRing using (BooleanRing ; BoolHom ; BooleanRingStr)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.BooleanRing.Initial using (BoolBR→ ; BoolBR→IsUnique)
open import BooleanRing.BooleanRingMaps using (idBoolHom)

open import BasicDefinitions 
open import BooleanRing.FreeBooleanRing.FreeBool 
open import StoneSpaces.Spectrum
open import BooleanRing.BooleanRingQuotients.UniversalProperty
open import Cubical.Foundations.Isomorphism
open import BooleanRing.BooleanRingQuotients.QuotientBool 
open import Countability.Properties 

------------------------------------------------------------------------
-- Bool (= the dualising object 2) arithmetic: + is xor.
------------------------------------------------------------------------
⊕≡false→≡ : (a b : Bool) → a ⊕ b ≡ false → a ≡ b
⊕≡false→≡ false false _ = refl
⊕≡false→≡ false true  p = ⊥.rec (true≢false p)
⊕≡false→≡ true  false p = ⊥.rec (true≢false p)
⊕≡false→≡ true  true  _ = refl

a⊕a≡false : (a : Bool) → a ⊕ a ≡ false
a⊕a≡false false = refl
a⊕a≡false true  = refl

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

  πB : BoolHom (freeBA GenB) B
  πB = quotientImageHom {B = freeBA GenB} {f = relB}
  
  _$gen_ : (SpGeneralBooleanRing B) → GenB → Bool
  x $gen g = (x ∘cr πB) $cr generator g 
  
  C : BooleanRing ℓ-zero
  C = freeBA GenC /Im relC

  πC : BoolHom (freeBA GenC) C
  πC = quotientImageHom {B = freeBA GenC} {f = relC}
  
  homAgreeOnGen→≡ : (h₁ h₂ : SpGeneralBooleanRing B)
                  → ((g : GenB) → h₁ $gen g ≡ h₂ $gen g) → h₁ ≡ h₂
  -- note this is useful later to note that equality in Stone spaces is closed.
  homAgreeOnGen→≡ h₁ h₂ agree =
    CommRingHom≡ (quotientImageHomEpi {f = relB} (Bool , isSetBool) (cong fst h₁πB≡h₂πB))
    where
      h₁πB≡h₂πB : h₁ ∘cr πB ≡ h₂ ∘cr πB
      h₁πB≡h₂πB = sym (inducedBAHomUnique GenB BoolBR (λ g → h₁ $gen g) (h₁ ∘cr πB) refl)
                ∙ cong (inducedBAHom GenB BoolBR) (funExt agree)
                ∙ inducedBAHomUnique GenB BoolBR (λ g → h₂ $gen g) (h₂ ∘cr πB) refl

  -- the initial inclusion ι : 2 → C
  ιC : Bool → ⟨ C ⟩
  ιC = fst (BoolBR→ C)
  
  private
    _+C_ : ⟨ C ⟩ → ⟨ C ⟩ → ⟨ C ⟩
    _+C_ = BooleanRingStr._+_ (snd C)

  -- γ ∘ ι is the identity on 2 (both are homs out of the initial BA 2)
  γ∘ι≡id : (γ : SpGeneralBooleanRing C) (b : Bool) → γ $cr (ιC b) ≡ b
  γ∘ι≡id γ b = funExt⁻ (BoolBR→IsUnique BoolBR (γ ∘cr BoolBR→ C)) b
             ∙ sym (funExt⁻ (BoolBR→IsUnique BoolBR (idBoolHom BoolBR)) b)

  module FibersOfSp (f : BoolHom B C) (x : SpGeneralBooleanRing B) where
    generatorsBsentTo0 : Type
    generatorsBsentTo0 = Σ[ g ∈ GenB ] (not (x $gen g) ≡ true)

    generatorsBsentTo0-count : has-Countability-structure generatorsBsentTo0
    generatorsBsentTo0-count = has-Countability-structure-Σ-Bool (not ∘ (x $gen_)) GenB-count

    fRestricted : generatorsBsentTo0 → ⟨ C ⟩
    fRestricted (g , _) = (f ∘cr πB) $cr generator g

    C/fRestricted : BooleanRing ℓ-zero
    C/fRestricted = C /Im fRestricted

    SpC/fRestricted≅ : Iso 
      (SpGeneralBooleanRing C/fRestricted)
      (Σ[ h ∈ SpGeneralBooleanRing C ] ((p : generatorsBsentTo0) → (h ∘cr f) $gen (fst p) ≡ false))
    SpC/fRestricted≅ = invIso (MapsOutOfQuotientUniversalProperty.mapsOutQuotientUniversalProperty C fRestricted BoolBR)

    ----------------------------------------------------------------
    -- The actual fibre.  To force  γ∘f = x  we must constrain EVERY generator, not
    -- just the x-zero ones: quotient C by  f(genB g) + ι(x g)  for all g
    -- (= f(genB g) when x(g)=0, and its complement f(genB g)+1 when x(g)=1).
    ----------------------------------------------------------------
    relFibre : GenB → ⟨ C ⟩
    relFibre g = ((f ∘cr πB) $cr generator g) +C ιC (x $gen g)

    C/fibre : BooleanRing ℓ-zero
    C/fibre = C /Im relFibre

    -- γ evaluates the g-th relation to the xor  (γ∘f)(g) ⊕ x(g)
    relFibre-eval : (γ : SpGeneralBooleanRing C) (g : GenB)
                  → γ $cr relFibre g ≡ ((γ ∘cr f) $gen g) ⊕ (x $gen g)
    relFibre-eval γ g =
      γ $cr relFibre g
        ≡⟨ IsCommRingHom.pres+ (snd γ) ((f ∘cr πB) $cr generator g) (ιC (x $gen g)) ⟩
      ((γ ∘cr f) $gen g) ⊕ (γ $cr ιC (x $gen g))
        ≡⟨ cong (((γ ∘cr f) $gen g) ⊕_) (γ∘ι≡id γ (x $gen g)) ⟩
      ((γ ∘cr f) $gen g) ⊕ (x $gen g) ∎

    -- γ respects all relations  ⟺  γ∘f = x
    resp↔fibre : (γ : SpGeneralBooleanRing C)
               → Iso ((g : GenB) → γ $cr relFibre g ≡ false) (γ ∘cr f ≡ x)
    resp↔fibre γ = isProp→Iso
      (isPropΠ (λ g → isSetBool _ _))
      (isSetBoolHom B BoolBR (γ ∘cr f) x)
      (λ resp → homAgreeOnGen→≡ (γ ∘cr f) x
         (λ g → ⊕≡false→≡ _ _ (sym (relFibre-eval γ g) ∙ resp g)))
      (λ eq g → relFibre-eval γ g
              ∙ cong (_⊕ (x $gen g)) (cong (λ h → h $gen g) eq)
              ∙ a⊕a≡false (x $gen g))

    private
      upFibre : Iso (Σ[ γ ∈ SpGeneralBooleanRing C ] ((g : GenB) → γ $cr relFibre g ≡ false))
                    (SpGeneralBooleanRing C/fibre)
      upFibre = MapsOutOfQuotientUniversalProperty.mapsOutQuotientUniversalProperty C relFibre BoolBR

    -- THE RESULT:  Sp(C/fibre) ≅ { γ ∈ Sp C ∣ γ ∘cr f = x }  (= fibre of SpAction f over x)
    SpC/fibre≅fibre : Iso (SpGeneralBooleanRing C/fibre)
                          (Σ[ γ ∈ SpGeneralBooleanRing C ] (γ ∘cr f ≡ x))
    SpC/fibre≅fibre = compIso (invIso upFibre) (Σ-cong-iso-snd resp↔fibre)

