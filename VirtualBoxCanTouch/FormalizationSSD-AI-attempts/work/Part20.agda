{-# OPTIONS --cubical --guardedness #-}

open import work.Part02Defs using (FoundationalAxioms)
import work.Part12

module work.Part20 (fa : FoundationalAxioms) (ia : work.Part12.IntervalAxioms fa) where

open import work.Part19 fa ia public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

-- tex Corollary 3047: R and D² are I-contractible
record RealAxioms : Type (ℓ-suc ℓ-zero) where
  open PathConnectedContractibleTC using (ContinuousPath)
  field
    R : Type ℓ-zero
    R-path-connected : (x y : R) → ContinuousPath x y
    D²-type : Type ℓ-zero
    D²-path-connected : (x y : D²-type) → ContinuousPath x y

module RealTheory (ra : RealAxioms) where
  open RealAxioms ra public
  open PathConnectedContractibleTC
  open BZILocalTC using (BZ-I-local)

  R-I-contractible : {Y : Type ℓ-zero}
    → ((g : UnitInterval → Y) → (a b : UnitInterval) → g a ≡ g b)
    → (r₀ : R) → (f : R → Y) → (r : R) → f r ≡ f r₀
  R-I-contractible Y-loc r₀ = path-connected→const r₀ (R-path-connected r₀) Y-loc

  D²-I-contractible : {Y : Type ℓ-zero}
    → ((g : UnitInterval → Y) → (a b : UnitInterval) → g a ≡ g b)
    → (d₀ : D²-type) → (f : D²-type → Y) → (d : D²-type) → f d ≡ f d₀
  D²-I-contractible Y-loc d₀ = path-connected→const d₀ (D²-path-connected d₀) Y-loc

  D²→BZ-const : (d₀ : D²-type) → (f : D²-type → BZ) → (d : D²-type) → f d ≡ f d₀
  D²→BZ-const = D²-I-contractible BZ-I-local

-- tex Proposition 3051 (shape-S1-is-BZ): L_I(R/Z) = BZ

-- tex Theorems 475, 530, 541: MP, LLPO, NOT-WLPO
module OmnisciencePrinciplesTC where
  open NotWLPOTC public using (¬WLPO)

-- tex Theorems 3082 and 3099: IVT and Brouwer FPT
module MainApplicationTheoremsModule (da : DiskAxioms) where
  open DiskTheory da public
    using (BrouwerFixedPointTheorem; Disk2)

  IntermediateValueTheorem' = IntermediateValueTheorem

