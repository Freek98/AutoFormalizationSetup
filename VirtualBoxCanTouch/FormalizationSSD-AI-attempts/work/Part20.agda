{-# OPTIONS --cubical --guardedness #-}

module work.Part20 where

open import work.Part19 public

-- tex Corollary 3047: R and D² are I-contractible
module RIContractibleTC where
  open PathConnectedContractibleTC using (ContinuousPath)

  postulate
    R : Type₀
    R-path-connected : (x y : R) → ContinuousPath x y
    D² : Type₀
    D²-path-connected : (x y : D²) → ContinuousPath x y

-- tex Corollary 3047 consequence: R and D² are I-contractible
-- Any function from R or D² to an I-local type is constant.
module IContractibleConsequences where
  open RIContractibleTC
  open PathConnectedContractibleTC
  open IntervalIsCHausModule using (UnitInterval)
  open IntervalTopologyModule using (0I; 1I)
  open CohomologyModule using (BZ)
  open BZILocalTC using (BZ-I-local)

  -- R is I-contractible: any f : R → Y with Y I-local is constant
  R-I-contractible : {Y : Type ℓ-zero}
    → ((g : UnitInterval → Y) → (a b : UnitInterval) → g a ≡ g b)
    → (r₀ : R) → (f : R → Y) → (r : R) → f r ≡ f r₀
  R-I-contractible Y-loc r₀ = path-connected→const r₀ (R-path-connected r₀) Y-loc

  -- D² is I-contractible: any f : D² → Y with Y I-local is constant
  D²-I-contractible : {Y : Type ℓ-zero}
    → ((g : UnitInterval → Y) → (a b : UnitInterval) → g a ≡ g b)
    → (d₀ : D²) → (f : D² → Y) → (d : D²) → f d ≡ f d₀
  D²-I-contractible Y-loc d₀ = path-connected→const d₀ (D²-path-connected d₀) Y-loc

  -- Key consequence: any f : D² → BZ is constant (since BZ is I-local)
  D²→BZ-const : (d₀ : D²) → (f : D² → BZ) → (d : D²) → f d ≡ f d₀
  D²→BZ-const = D²-I-contractible BZ-I-local

-- tex Proposition 3051 (shape-S1-is-BZ): L_I(R/Z) = BZ
-- Proof: fibers of R→R/Z are Z-torsors, giving pullback square.
-- BZ is I-local (BZ-I-local), R is I-contractible (R-I-contractible),
-- so the bottom map R/Z → BZ is an I-localization.
-- (Formal statement requires localization infrastructure beyond current formalization.)

-- tex Theorems 475, 530, 541: MP, LLPO, NOT-WLPO
module OmnisciencePrinciplesTC where
  open NotWLPOTC public using (¬WLPO)

-- tex Theorems 3082 and 3099: IVT and Brouwer FPT
module MainApplicationTheoremsTC where
  open IntermediateValueTheoremModule public
    using (IntermediateValueTheorem)

  open BrouwerFixedPointTheoremModule public
    using (BrouwerFixedPointTheorem; Disk2; Circle)
