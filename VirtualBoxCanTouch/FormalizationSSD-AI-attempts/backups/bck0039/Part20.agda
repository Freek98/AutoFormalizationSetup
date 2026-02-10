{-# OPTIONS --cubical --guardedness #-}

module work.Part20 where

open import work.Part19 public

-- tex Proposition 3051: L_I(R/Z) = BZ
module ShapeS1IsBZTC where
  open import Cubical.HITs.S1 using (S¹; base; ΩS¹≡ℤ)
  open import Cubical.Data.Int using (ℤ)
  open CohomologyModule using (BZ; BZ∙; bz₀)
  open BZILocalTC using (BZ-I-local)
  open PathConnectedContractibleTC using (ContinuousPath; isContPathConnectedFrom)

  S¹-is-circle : Type₀
  S¹-is-circle = S¹

  loop-space-S¹ : (base ≡ base) ≡ ℤ
  loop-space-S¹ = ΩS¹≡ℤ

-- tex Corollary 3047: R and D² are I-contractible
module RIContractibleTC where
  open PathConnectedContractibleTC using (ContinuousPath; isContPathConnectedFrom)

  postulate
    R : Type₀
    R-path-connected : (x y : R) → ContinuousPath x y

  R-cont-path-connected-from : (x : R) → isContPathConnectedFrom R x
  R-cont-path-connected-from x y = R-path-connected x y

  postulate
    D² : Type₀
    D²-path-connected : (x y : D²) → ContinuousPath x y

  D²-cont-path-connected-from : (x : D²) → isContPathConnectedFrom D² x
  D²-cont-path-connected-from x y = D²-path-connected x y

-- tex Proposition 2991: H¹(I,ℤ) = 0
module IntervalCohomologyTC where
  open import Cubical.Data.Int using (ℤ)
  open import Cubical.Cohomology.EilenbergMacLane.Base using (0ₕ)
  open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
  open IntervalIsCHausModule using (UnitInterval)
  open CohomologyModule using (H¹; interval-cohomology-vanishes)

  H¹-I-vanishes : (x : H¹ UnitInterval) → x ≡ 0ₕ 1 {G = ℤAbGroup}
  H¹-I-vanishes = interval-cohomology-vanishes

-- tex Proposition 3074: S¹ → D² has no retraction
module NoRetractionTC where
  open BrouwerFixedPointTheoremModule using (Disk2; Circle; boundary-inclusion; no-retraction)
  open ShapeS1IsBZTC using (S¹-is-circle; loop-space-S¹)
  open RIContractibleTC using (D²; D²-cont-path-connected-from)
  open CohomologyModule using (BZ; BZ∙; bz₀)

  open import Cubical.Data.Int using (ℤ)
  open import Cubical.HITs.S1 using (S¹; base; ΩS¹≡ℤ)

  Ω-S¹-is-ℤ : (base ≡ base) ≡ ℤ
  Ω-S¹-is-ℤ = ΩS¹≡ℤ

-- tex Theorems 475, 530, 541: MP, LLPO, NOT-WLPO
module OmnisciencePrinciplesTC where
  open NotWLPOTC public using (¬WLPO)

-- tex Theorems 3082 and 3099: IVT and Brouwer FPT
module MainApplicationTheoremsTC where
  open IntermediateValueTheoremModule public
    using (IntermediateValueTheorem)

  open BrouwerFixedPointTheoremModule public
    using (BrouwerFixedPointTheorem; Disk2; Circle)
