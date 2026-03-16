{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module OvertlyDiscrete.ProductClosure where

-- This file shows that countably presented Boolean rings are closed
-- under products, using the overtly discrete characterization.
--
-- The proof goes:
-- 1. CP(B₁) and CP(B₂) → ⟨B₁⟩ and ⟨B₂⟩ are overtly discrete
-- 2. Product of overtly discrete types is overtly discrete
-- 3. ⟨ B₁ ×BR B₂ ⟩ = ⟨B₁⟩ × ⟨B₂⟩ is overtly discrete
-- 4. Therefore B₁ ×BR B₂ is countably presented

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing

open import BooleanRing.Products
open import CountablyPresentedBooleanRings.Definitions

open import OvertlyDiscrete.Definition
open import OvertlyDiscrete.BooleOmegaEquiv

-- ════════════════════════════════════════════════════════════════
-- Key observation: ⟨ A ×BR B ⟩ ≡ ⟨ A ⟩ × ⟨ B ⟩ (definitionally)
-- ════════════════════════════════════════════════════════════════

-- The underlying type of A ×BR B is literally ⟨A⟩ × ⟨B⟩ by definition
-- of _×BR_ in BooleanRing.Products. So transport is trivial.

-- ════════════════════════════════════════════════════════════════
-- Main theorem: products preserve countable presentability
-- ════════════════════════════════════════════════════════════════

Booleω-closed-×BR : (A B : BooleanRing ℓ-zero)
  → is-countably-presented-alt A
  → is-countably-presented-alt B
  → is-countably-presented-alt (A ×BR B)
Booleω-closed-×BR A B cpA cpB = OD→CP (A ×BR B) odAB
  where
  -- Step 1: Underlying types are overtly discrete
  odA : isOvertlyDiscrete ⟨ A ⟩
  odA = CP→OD A cpA

  odB : isOvertlyDiscrete ⟨ B ⟩
  odB = CP→OD B cpB

  -- Step 2: Product of overtly discrete types is overtly discrete
  odAB : isOvertlyDiscrete ⟨ A ×BR B ⟩
  odAB = isODisc-× odA odB
  -- Note: ⟨ A ×BR B ⟩ = ⟨ A ⟩ × ⟨ B ⟩ definitionally,
  -- so isODisc-× applies directly.
