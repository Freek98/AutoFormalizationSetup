{-# OPTIONS --cubical --guardedness #-}

module SSD.All where

open import SSD.Applications.Applications public

open import Cubical.Foundations.Prelude

module WithAxiomsAll (axioms : Axioms) where
  open WithAxioms axioms
  open OpenClosedProperties axioms
  open WithAxiomsCPS axioms
  open WithAxiomsSEC axioms
  open WithAxiomsSP axioms
  open WithAxiomsSACC axioms
  open WithAxiomsCH axioms
  open WithAxiomsInt axioms
  open WithAxiomsBFPT axioms
  open WithAxiomsCoh axioms
  open WithAxiomsApp axioms

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
