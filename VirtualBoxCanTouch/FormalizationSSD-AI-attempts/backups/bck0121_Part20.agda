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

-- tex Theorems 475, 530, 541: MP, LLPO, NOT-WLPO
module OmnisciencePrinciplesTC where
  open NotWLPOTC public using (¬WLPO)

-- tex Theorems 3082 and 3099: IVT and Brouwer FPT
module MainApplicationTheoremsTC where
  open IntermediateValueTheoremModule public
    using (IntermediateValueTheorem)

  open BrouwerFixedPointTheoremModule public
    using (BrouwerFixedPointTheorem; Disk2; Circle)
