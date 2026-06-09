module DCTopologyApplications where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Nat using (ℕ)
import Cubical.HITs.PropositionalTruncation as PT

open import PropositionalTopology.Definitions
open import PropositionalTopology.Properties
open import Axioms.DependentChoice

module assumingCC (countableChoice : CountableChoice {ℓ-zero}) where
  -- a countable disjunction of open propositions is open
  Openℕ⊔ : (P : ℕ → hProp ℓ-zero) → ((n : ℕ) → isOpenProp (P n)) → isOpenProp (ℕ⊔ P)
  Openℕ⊔ P opens =
    PT.map (OpenWitnessℕ⊔ P) (countableChoice (λ n → isOpenWitness (P n)) opens)

  -- a countable conjunction of closed propositions is closed
  Closedℕ⊓ : (P : ℕ → hProp ℓ-zero) → ((n : ℕ) → isClosedProp (P n)) → isClosedProp (ℕ⊓ P)
  Closedℕ⊓ P closeds =
    PT.map (ClosedWitnessℕ⊓ P) (countableChoice (λ n → isClosedWitness (P n)) closeds)
