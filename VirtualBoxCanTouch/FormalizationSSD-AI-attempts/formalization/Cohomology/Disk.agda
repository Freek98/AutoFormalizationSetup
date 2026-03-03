{-# OPTIONS --cubical --guardedness #-}

open import formalization.StoneDuality.AxiomDefs using (FoundationalAxioms)
import formalization.CompactHausdorff.Interval

module formalization.Cohomology.Disk (fa : FoundationalAxioms) (ia : formalization.CompactHausdorff.Interval.IntervalAxioms fa) where

open import formalization.CompactHausdorff.Interval fa public
open IntervalTheory ia public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; squash₁; ∣_∣₁)

record DiskAxioms : Type (ℓ-suc ℓ-zero) where
  open CompactHausdorffModule
  field
    Disk2 : Type ℓ-zero
    isSetDisk2 : isSet Disk2
    Circle : Type ℓ-zero
    boundary-inclusion : Circle → Disk2
    Disk2IsCHaus : hasCHausStr Disk2
    -- tex Proposition 3073
    no-retraction : (r : Disk2 → Circle)
      → ((x : Circle) → r (boundary-inclusion x) ≡ x)
      → ⊥
    retraction-from-no-fixpoint : (f : Disk2 → Disk2)
      → ((x : Disk2) → (f x ≡ x → ⊥))
      → Σ[ r ∈ (Disk2 → Circle) ] ((x : Circle) → r (boundary-inclusion x) ≡ x)

module DiskTheory (da : DiskAxioms) where
  open DiskAxioms da public
  open CompactHausdorffModule
  open InhabitedClosedSubSpaceClosedCHausModule

  Disk2CHaus : CHaus
  Disk2CHaus = Disk2 , Disk2IsCHaus

  BFP-contradiction : (f : Disk2 → Disk2) → ((x : Disk2) → (f x ≡ x → ⊥)) → ⊥
  BFP-contradiction f no-fix =
    let (r , rr) = retraction-from-no-fixpoint f no-fix in no-retraction r rr

  -- tex Theorem 3099
  BrouwerFixedPointTheorem : (f : Disk2 → Disk2)
    → ∥ Σ[ x ∈ Disk2 ] f x ≡ x ∥₁
  BrouwerFixedPointTheorem f =
    let
        existence-prop : hProp ℓ-zero
        existence-prop = (∥ Σ[ x ∈ Disk2 ] f x ≡ x ∥₁) , squash₁

        A : Disk2 → hProp ℓ-zero
        A x = (f x ≡ x) , isSetDisk2 (f x) x

        A-closed : (x : Disk2) → isClosedProp (A x)
        A-closed x = hasCHausStr.equalityClosed Disk2IsCHaus (f x) x

        existence-closed : isClosedProp existence-prop
        existence-closed = InhabitedClosedSubSpaceClosedCHaus Disk2CHaus A A-closed

        ¬¬existence : ¬ ¬ ∥ Σ[ x ∈ Disk2 ] f x ≡ x ∥₁
        ¬¬existence ¬∃ = BFP-contradiction f (λ x fx=x → ¬∃ ∣ x , fx=x ∣₁)

    in closedIsStable existence-prop existence-closed ¬¬existence
