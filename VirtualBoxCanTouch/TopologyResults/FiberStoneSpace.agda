{-# OPTIONS --lossy-unification #-}
-- The fibre of Sp(f) : Sp C → Sp B over a point x : Sp B as the spectrum of a
-- Boolean algebra.  This is the geometric heart of "propositional completeness ⟹
-- formal surjections are surjective": given f : B → C and x : Sp B, the fibre
-- Sp(f)⁻¹(x) is itself a Stone space, namely Sp(Dₓ) where Dₓ is the pushout
--
--        B ─ f ─▶ C
--        │        │
--        x        │            Dₓ = C ⊗_B 2   (pushout of f and x)
--        ▼        ▼
--        2 ─────▶ Dₓ
--
-- Concretely Dₓ is C with the relations  f(b) = x(b)  imposed for b ∈ B; since both
-- sides are homomorphisms it suffices to impose this on a generating family of B,
-- i.e. Dₓ = C /Im (n ↦ f(gₙ) + ι(x gₙ)) where gₙ are generators of B and ι : 2 → C
-- is the (initial) inclusion.  By the universal property of the quotient, a point
-- g : C → 2 descends to Dₓ iff it kills every relation iff g∘f = x — i.e.
--      Sp(Dₓ) ≅ { g : Sp C ∣ g ∘ f = x } = fibre of Sp(f) over x.
--
-- This file (a starting point) fixes B by a generating surjection pB : freeBA ℕ ↠ B
-- (every countably presented B has one) and proves the iso above.  Countable
-- presentation of Dₓ is treated in the companion section at the bottom.
module FiberStoneSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool using (Bool ; true ; false ; _⊕_ ; true≢false ; isSetBool)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
open import Cubical.Functions.Surjection using (isSurjection)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

open import Cubical.Algebra.CommRing using (_$cr_ ; _∘cr_ ; CommRingHom≡ ; IsCommRingHom)
open import Cubical.Algebra.BooleanRing using (BooleanRing ; BooleanRingStr ; BoolHom)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.BooleanRing.Initial using (BoolBR→ ; BoolBR→IsUnique)

open import BooleanRing.BooleanRingMaps using (idBoolHom)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA ; generator ; inducedBAHom ; inducedBAHomUnique)
open import BooleanRing.BooleanRingQuotients.QuotientBool using (_/Im_)
open import BooleanRing.BooleanRingQuotients.UniversalProperty
open import StoneSpaces.Spectrum using (SpGeneralBooleanRing ; isSetBoolHom)

------------------------------------------------------------------------
-- Bool (= the dualising object 2) arithmetic: + is xor, 𝟘 is false.
------------------------------------------------------------------------

⊕≡false→≡ : (a b : Bool) → a ⊕ b ≡ false → a ≡ b
⊕≡false→≡ false false _ = refl
⊕≡false→≡ false true  p = Empty.rec (true≢false p)
⊕≡false→≡ true  false p = Empty.rec (true≢false p)
⊕≡false→≡ true  true  _ = refl

a⊕a≡false : (a : Bool) → a ⊕ a ≡ false
a⊕a≡false false = refl
a⊕a≡false true  = refl

------------------------------------------------------------------------
-- The construction, for B presented by a generating surjection pB.
------------------------------------------------------------------------

module Fibre
  (B C : BooleanRing ℓ-zero)
  (pB : BoolHom (freeBA ℕ) B) (pBsurj : isSurjection (fst pB))
  (f : BoolHom B C)
  (x : BoolHom B BoolBR)
  where

  -- generators of B
  genB : ℕ → ⟨ B ⟩
  genB n = fst pB (generator n)

  -- the initial inclusion ι : 2 → C  (false ↦ 0, true ↦ 1)
  ιC : Bool → ⟨ C ⟩
  ιC = fst (BoolBR→ C)

  private
    _+C_ : ⟨ C ⟩ → ⟨ C ⟩ → ⟨ C ⟩
    _+C_ = BooleanRingStr._+_ (snd C)

  -- the relations cutting C down to the fibre over x
  relx : ℕ → ⟨ C ⟩
  relx n = (f $cr genB n) +C ιC (x $cr genB n)

  -- the fibre Boolean algebra  Dₓ = C ⊗_B 2  (pushout of f and x)
  Dx : BooleanRing ℓ-zero
  Dx = C /Im relx

  ----------------------------------------------------------------------
  -- Two homs B → 2 agreeing on the generators gₙ are equal.
  -- (pB is epi, and homs out of freeBA ℕ are determined by their values on
  --  the generators.)
  ----------------------------------------------------------------------
  homAgreeOnGen→≡ : (h₁ h₂ : BoolHom B BoolBR)
                  → ((n : ℕ) → h₁ $cr genB n ≡ h₂ $cr genB n) → h₁ ≡ h₂
  homAgreeOnGen→≡ h₁ h₂ agree = epi (sym ind₁ ∙ cong (inducedBAHom ℕ BoolBR) (funExt agree) ∙ ind₂)
    where
      ind₁ : inducedBAHom ℕ BoolBR (λ n → h₁ $cr genB n) ≡ h₁ ∘cr pB
      ind₁ = inducedBAHomUnique ℕ BoolBR (λ n → h₁ $cr genB n) (h₁ ∘cr pB) refl
      ind₂ : inducedBAHom ℕ BoolBR (λ n → h₂ $cr genB n) ≡ h₂ ∘cr pB
      ind₂ = inducedBAHomUnique ℕ BoolBR (λ n → h₂ $cr genB n) (h₂ ∘cr pB) refl
      epi : (h₁ ∘cr pB ≡ h₂ ∘cr pB) → h₁ ≡ h₂
      epi p = CommRingHom≡ (funExt λ b →
        PT.rec (isSetBool _ _)
          (λ (a , pa) → cong (fst h₁) (sym pa) ∙ funExt⁻ (cong fst p) a ∙ cong (fst h₂) pa)
          (pBsurj b))

  ----------------------------------------------------------------------
  -- g ∘ ι is the identity on 2 (both are homs out of the initial BA 2).
  ----------------------------------------------------------------------
  g∘ι≡id : (g : BoolHom C BoolBR) (b : Bool) → g $cr (ιC b) ≡ b
  g∘ι≡id g b =
      funExt⁻ (BoolBR→IsUnique BoolBR (g ∘cr BoolBR→ C)) b
    ∙ sym (funExt⁻ (BoolBR→IsUnique BoolBR (idBoolHom BoolBR)) b)

  ----------------------------------------------------------------------
  -- A point g : C → 2 evaluates the n-th relation to the xor
  --   (g∘f)(gₙ) ⊕ x(gₙ).
  ----------------------------------------------------------------------
  relx-eval : (g : BoolHom C BoolBR) (n : ℕ)
            → g $cr relx n ≡ (g $cr (f $cr genB n)) ⊕ (x $cr genB n)
  relx-eval g n =
    g $cr relx n
      ≡⟨ IsCommRingHom.pres+ (snd g) (f $cr genB n) (ιC (x $cr genB n)) ⟩
    (g $cr (f $cr genB n)) ⊕ (g $cr (ιC (x $cr genB n)))
      ≡⟨ cong ((g $cr (f $cr genB n)) ⊕_) (g∘ι≡id g (x $cr genB n)) ⟩
    (g $cr (f $cr genB n)) ⊕ (x $cr genB n) ∎

  ----------------------------------------------------------------------
  -- g respects all relations  ⟺  g ∘ f = x.
  ----------------------------------------------------------------------
  RespRel : BoolHom C BoolBR → Type
  RespRel g = (n : ℕ) → g $cr relx n ≡ false

  resp↔fibre : (g : BoolHom C BoolBR) → Iso (RespRel g) (g ∘cr f ≡ x)
  resp↔fibre g = isProp→Iso
    (isPropΠ (λ n → isSetBool _ _))
    (isSetBoolHom B BoolBR (g ∘cr f) x)
    toFib
    fromFib
    where
      toFib : RespRel g → (g ∘cr f ≡ x)
      toFib resp = homAgreeOnGen→≡ (g ∘cr f) x
        (λ n → ⊕≡false→≡ _ _ (sym (relx-eval g n) ∙ resp n))
      fromFib : (g ∘cr f ≡ x) → RespRel g
      fromFib eq n =
          relx-eval g n
        ∙ cong (_⊕ (x $cr genB n)) (cong (λ h → h $cr genB n) eq)
        ∙ a⊕a≡false (x $cr genB n)

  ----------------------------------------------------------------------
  -- Sp(Dₓ) ≅ fibre of Sp(f) over x.
  --
  -- Sp(Dₓ) = BoolHom Dₓ 2.  The quotient universal property identifies it with the
  -- relation-respecting points of C, which resp↔fibre identifies with the fibre.
  ----------------------------------------------------------------------

  -- fibre of  Sp(f) : Sp C → Sp B ,  g ↦ g ∘cr f ,  over x
  fibreOver-x : Type
  fibreOver-x = Σ[ g ∈ BoolHom C BoolBR ] (g ∘cr f ≡ x)

  private
    upIso : Iso (Σ[ g ∈ BoolHom C BoolBR ] ((n : ℕ) → g $cr relx n ≡ false))
                (BoolHom Dx BoolBR)
    upIso = MapsOutOfQuotientUniversalProperty.mapsOutQuotientUniversalProperty C relx BoolBR

  SpDx≅fibre : Iso (BoolHom Dx BoolBR) fibreOver-x
  SpDx≅fibre = compIso (invIso upIso) (Σ-cong-iso-snd resp↔fibre)

  -- … and Sp(Dₓ) is literally SpGeneralBooleanRing Dₓ:
  SpDx≅fibre' : Iso (SpGeneralBooleanRing Dx) fibreOver-x
  SpDx≅fibre' = SpDx≅fibre
