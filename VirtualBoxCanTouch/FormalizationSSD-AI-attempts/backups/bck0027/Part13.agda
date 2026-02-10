{-# OPTIONS --cubical --guardedness #-}

module work.Part13 where

open import work.Part12 public

import Cubical.HITs.PropositionalTruncation as PT

module BrouwerFixedPointTheoremModule where
  open InhabitedClosedSubSpaceClosedCHausModule
  open IntervalIsCHausModule
  open CompactHausdorffModule

  postulate
    Disk2 : Type₀
    isSetDisk2 : isSet Disk2

  postulate
    Circle : Type₀
    isSetCircle : isSet Circle

  postulate
    boundary-inclusion : Circle → Disk2

  -- D² is compact Hausdorff (tex: follows from being homeomorphic to I²)
  postulate
    Disk2IsCHaus : hasCHausStr Disk2

  -- D² is contractible (tex Corollary 3047 R-I-contractible)
  postulate
    isContrDisk2 : isContr Disk2

  Disk2CHaus : CHaus
  Disk2CHaus = Disk2 , Disk2IsCHaus

  -- No retraction from D² to S¹ (tex Proposition 3074)
  postulate
    no-retraction : (r : Disk2 → Circle)
      → ((x : Circle) → r (boundary-inclusion x) ≡ x)
      → ⊥

  postulate
    retraction-from-no-fixpoint : (f : Disk2 → Disk2)
      → ((x : Disk2) → (f x ≡ x → ⊥))
      → Σ[ r ∈ (Disk2 → Circle) ] ((x : Circle) → r (boundary-inclusion x) ≡ x)

  BFP-contradiction : (f : Disk2 → Disk2)
    → ((x : Disk2) → (f x ≡ x → ⊥))
    → ⊥
  BFP-contradiction f no-fix =
    let (r , r-is-retract) = retraction-from-no-fixpoint f no-fix
    in no-retraction r r-is-retract

  -- tex Theorem 3099
  BrouwerFixedPointTheorem : (f : Disk2 → Disk2)
    → ∥ Σ[ x ∈ Disk2 ] f x ≡ x ∥₁
  BrouwerFixedPointTheorem f =
    let -- The proposition "∃x. f(x) = x"
        existence-prop : hProp ℓ-zero
        existence-prop = (∥ Σ[ x ∈ Disk2 ] f x ≡ x ∥₁) , squash₁

        A : Disk2 → hProp ℓ-zero
        A x = (f x ≡ x) , isSetDisk2 (f x) x

        A-closed : (x : Disk2) → isClosedProp (A x)
        A-closed x = hasCHausStr.equalityClosed Disk2IsCHaus (f x) x

        existence-closed : isClosedProp existence-prop
        existence-closed = InhabitedClosedSubSpaceClosedCHaus Disk2CHaus A A-closed

        ¬¬existence : ¬ ¬ ∥ Σ[ x ∈ Disk2 ] f x ≡ x ∥₁
        ¬¬existence ¬∃ =
          let no-fix : (x : Disk2) → (f x ≡ x → ⊥)
              no-fix x fx=x = ¬∃ ∣ x , fx=x ∣₁
          in BFP-contradiction f no-fix

    in closedIsStable existence-prop existence-closed ¬¬existence

module ClosedInStoneIsStoneProof where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isPropHasStoneStr; isSetBoolHom)
  open SDDecToElemModule
  open StoneClosedSubsetsModule

  ClosedInStoneIsStone-proved : (S : Stone) → (A : fst S → hProp ℓ-zero)
                              → ((x : fst S) → isClosedProp (A x))
                              → hasStoneStr (Σ (fst S) (λ x → fst (A x)))
  ClosedInStoneIsStone-proved S A A-closed =
    PT.rec (isPropHasStoneStr sd-axiom _) construct (snd (fst (snd S)))
    where
    |S| : Type ℓ-zero
    |S| = fst S

    S-isSet : isSet |S|
    S-isSet = subst isSet (snd (snd S)) (isSetBoolHom (fst (fst (snd S))) BoolBR)

    ΣA-isSet : isSet (Σ |S| (λ x → fst (A x)))
    ΣA-isSet = isSetΣ S-isSet (λ x → isProp→isSet (snd (A x)))

    α : |S| → ℕ → Bool
    α x = fst (A-closed x)

    A→allFalse : (x : |S|) → fst (A x) → (n : ℕ) → α x n ≡ false
    A→allFalse x = fst (snd (A-closed x))

    allFalse→A : (x : |S|) → ((n : ℕ) → α x n ≡ false) → fst (A x)
    allFalse→A x = snd (snd (A-closed x))

    construct : has-Boole-ω' (fst (fst (snd S))) → hasStoneStr (Σ |S| (λ x → fst (A x)))
    construct (f₀ , equiv₀) = PT.rec propHasStoneStrΣA extractC (quotientBySeqPreservesBooleω B d)
      where
      propHasStoneStrΣA : isProp (hasStoneStr (Σ |S| (λ x → fst (A x))))
      propHasStoneStrΣA = isPropHasStoneStr sd-axiom (Σ |S| (λ x → fst (A x)))

      B : Booleω
      B = fst (snd S)

      SpB≡S : Sp B ≡ |S|
      SpB≡S = snd (snd S)

      α' : Sp B → ℕ → Bool
      α' x n = α (transport SpB≡S x) n

      D : ℕ → Sp B → Bool
      D n x = α' x n

      d : ℕ → ⟨ fst B ⟩
      d n = elemFromDecPred sd-axiom B (D n)

      d-property : (n : ℕ) (x : Sp B) → fst x (d n) ≡ α' x n
      d-property n x = decPred-elem-correspondence sd-axiom B (D n) x

      extractC : Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)))
               → hasStoneStr (Σ |S| (λ x → fst (A x)))
      extractC (C , SpC≃ClosedSubset) = C , SpC≡ΣA
        where
        ClosedSubsetB : Type ℓ-zero
        ClosedSubsetB = Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)

        ClosedSubsetB→ΣA : ClosedSubsetB → Σ |S| (λ y → fst (A y))
        ClosedSubsetB→ΣA (x , all-zero) = transport SpB≡S x , allFalse→A (transport SpB≡S x) allFalse'
          where
          allFalse' : (n : ℕ) → α (transport SpB≡S x) n ≡ false
          allFalse' n =
            α (transport SpB≡S x) n   ≡⟨ sym (d-property n x) ⟩
            fst x (d n)               ≡⟨ all-zero n ⟩
            false ∎

        ΣA→ClosedSubsetB : Σ |S| (λ y → fst (A y)) → ClosedSubsetB
        ΣA→ClosedSubsetB (y , Ay) = x , all-zero
          where
          x : Sp B
          x = transport (sym SpB≡S) y

          all-zero : (n : ℕ) → fst x (d n) ≡ false
          all-zero n =
            fst x (d n)             ≡⟨ d-property n x ⟩
            α' x n                  ≡⟨ refl ⟩
            α (transport SpB≡S x) n ≡⟨ cong (λ z → α z n) (transportTransport⁻ SpB≡S y) ⟩
            α y n                   ≡⟨ A→allFalse y Ay n ⟩
            false ∎

        open import Cubical.Foundations.Transport using (transport⁻Transport)
        ClosedSubsetB→ΣA→ClosedSubsetB : (xa : ClosedSubsetB) → ΣA→ClosedSubsetB (ClosedSubsetB→ΣA xa) ≡ xa
        ClosedSubsetB→ΣA→ClosedSubsetB (x , all-zero) =
          Σ≡Prop (λ _ → isPropΠ (λ _ → isSetBool _ _))
                 (transport⁻Transport SpB≡S x)

        ΣA→ClosedSubsetB→ΣA : (yAy : Σ |S| (λ y → fst (A y))) → ClosedSubsetB→ΣA (ΣA→ClosedSubsetB yAy) ≡ yAy
        ΣA→ClosedSubsetB→ΣA (y , Ay) =
          Σ≡Prop (λ z → snd (A z))
                 (transportTransport⁻ SpB≡S y)

        ClosedSubsetB≃ΣA : ClosedSubsetB ≃ Σ |S| (λ y → fst (A y))
        ClosedSubsetB≃ΣA = isoToEquiv (iso ClosedSubsetB→ΣA ΣA→ClosedSubsetB ΣA→ClosedSubsetB→ΣA ClosedSubsetB→ΣA→ClosedSubsetB)

        SpC≃ΣA : Sp C ≃ Σ |S| (λ y → fst (A y))
        SpC≃ΣA = compEquiv SpC≃ClosedSubset ClosedSubsetB≃ΣA

        SpC≡ΣA : Sp C ≡ Σ |S| (λ y → fst (A y))
        SpC≡ΣA = ua SpC≃ΣA

module ClosedInStoneIsStoneEqualityModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isPropHasStoneStr)
  open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2; isPropΠ3)
  open ClosedInStoneIsStoneModule
  open ClosedInStoneIsStoneProof

  isProp-ClosedInStoneIsStone-type : isProp ((S : Stone) → (A : fst S → hProp ℓ-zero)
                                            → ((x : fst S) → isClosedProp (A x))
                                            → hasStoneStr (Σ (fst S) (λ x → fst (A x))))
  isProp-ClosedInStoneIsStone-type =
    isPropΠ3 (λ S A _ → isPropHasStoneStr sd-axiom (Σ (fst S) (λ x → fst (A x))))

  ClosedInStoneIsStone-equality : ClosedInStoneIsStone ≡ ClosedInStoneIsStone-proved
  ClosedInStoneIsStone-equality = isProp-ClosedInStoneIsStone-type ClosedInStoneIsStone ClosedInStoneIsStone-proved

-- Section 6: Cohomology (tex 2769-2968)
-- Key results from the tex file:
-- - Čech complex C(S,T,A) (tex 2784-2795) - DEFINED
-- - section-exact-cech-complex (tex Lemma 2807) - PROVED!
-- - canonical-exact-cech-complex (tex Lemma 2815) - PROVED!
-- - exact-cech-complex-vanishing-cohomology (tex Lemma 2823) - PROVED!
-- - cech-complex-vanishing-stone (tex Lemma 2878) - postulate with proof sketch
-- - eilenberg-stone-vanish: H^1(S,Z) = 0 for Stone S (tex 2887) - postulate with proof deps
-- - stone-commute-delooping: B(Z^S) ≃ (BZ)^S (tex 2895) - postulate
-- - cech-eilenberg-1-agree: H^1(X,Z) = Ȟ^1(X,S,Z) (tex 2945) - postulate
-- - interval-cohomology-vanishes (tex Prop 2991) - DERIVED from isContrUnitInterval (CHANGES0323)
-- - Cn-exact-sequence (tex Lemma 2973) - finite approx module added
