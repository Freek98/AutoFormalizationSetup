{-# OPTIONS --cubical --guardedness #-}

module work.Part13 where

open import work.Part12 public

module BrouwerFixedPointTheoremModule where
  open InhabitedClosedSubSpaceClosedCHausModule
  open CompactHausdorffModule

  postulate
    Disk2 : Type₀
    isSetDisk2 : isSet Disk2
    Circle : Type₀
    boundary-inclusion : Circle → Disk2

  -- D² is compact Hausdorff (tex: follows from being homeomorphic to I²)
  postulate
    Disk2IsCHaus : hasCHausStr Disk2

  Disk2CHaus : CHaus
  Disk2CHaus = Disk2 , Disk2IsCHaus

  -- No retraction from D² to S¹ (tex Proposition 3074)
  postulate
    no-retraction : (r : Disk2 → Circle)
      → ((x : Circle) → r (boundary-inclusion x) ≡ x)
      → ⊥
    retraction-from-no-fixpoint : (f : Disk2 → Disk2)
      → ((x : Disk2) → (f x ≡ x → ⊥))
      → Σ[ r ∈ (Disk2 → Circle) ] ((x : Circle) → r (boundary-inclusion x) ≡ x)

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

-- Cohomology (tex 2769-2968)
