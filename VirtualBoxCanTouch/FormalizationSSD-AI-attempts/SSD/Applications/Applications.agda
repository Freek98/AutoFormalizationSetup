{-# OPTIONS --cubical --guardedness #-}

module SSD.Applications.Applications where

open import SSD.Cohomology.Cohomology public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (invEq; secEq; isEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Relation.Nullary using (¬_; yes; no)
open import Cubical.Algebra.CommRing using (CommRingHom≡; _$cr_)
import Cubical.HITs.PropositionalTruncation as PT
open PT using (∥_∥₁; ∣_∣₁; squash₁)

module WithAxiomsApp (axioms : Axioms) where
  open WithAxioms axioms
  open OpenClosedProperties axioms
  open WithAxiomsCPS axioms
  open WithAxiomsSEC axioms
  open WithAxiomsSP axioms
  open WithAxiomsCH axioms
  open WithAxiomsInt axioms
  open WithAxiomsBFPT axioms
  open WithAxiomsCoh axioms

  -- tex Remark after Lemma 3015: Stone spaces are I-local
  module StoneILocalTC where
    open ZILocalModule using (Bool-I-local)
    open IntervalIsCHausModule using (UnitInterval)

    funspace-I-local : {A : Type ℓ-zero} {B : Type ℓ-zero}
      → isSet A
      → ((f : UnitInterval → B) → (x y : UnitInterval) → f x ≡ f y)
      → (g : UnitInterval → (A → B))
      → (x y : UnitInterval) → g x ≡ g y
    funspace-I-local {A} {B} setA B-local g x y = funExt (λ a → B-local (λ i → g i a) x y)

    open import SSD.Library.StoneDuality using (Sp; Booleω)
    open import Cubical.Algebra.BooleanRing using (BooleanRingStr)

    Stone-Sp-I-local : (B : Booleω) → (f : UnitInterval → Sp B)
      → (x y : UnitInterval) → f x ≡ f y
    Stone-Sp-I-local B f x y =
      CommRingHom≡ (funspace-I-local (BooleanRingStr.is-set (snd (fst B))) Bool-I-local
                     (λ i → fst (f i)) x y)

  -- tex Lemma 3027: BZ is I-local
  module BZILocalTC where
    open CohomologyModule using (BZ)
    open IntervalIsCHausModule using (UnitInterval; isContrUnitInterval)

    BZ-I-local : (f : UnitInterval → BZ) → (x y : UnitInterval) → f x ≡ f y
    BZ-I-local = ZILocalModule.contr-map-const-local isContrUnitInterval

  -- tex Lemma 3035: continuously-path-connected-contractible
  module PathConnectedContractibleTC where
    open IntervalIsCHausModule using (UnitInterval)
    open IntervalTopologyModule using (0I; 1I)

    ContinuousPath : {X : Type ℓ-zero} → X → X → Type ℓ-zero
    ContinuousPath {X} x y = Σ[ f ∈ (UnitInterval → X) ] (f 0I ≡ x) × (f 1I ≡ y)

    isContPathConnectedFrom : (X : Type ℓ-zero) → X → Type ℓ-zero
    isContPathConnectedFrom X x = (y : X) → ContinuousPath x y

  -- tex Theorem 475: ¬WLPO from Stone Duality
  module NotWLPOTC where
    import SSD.Library.WLPO as WLPOmod
    open CantorIsStoneModule
    open import SSD.Library.StoneDuality using (evaluationMap; Sp; Booleω)
    open import SSD.Library.FreeBooleanRing.FreeBool using (freeBA)

    SD-freeBA-ℕ : isEquiv (evaluationMap freeBA-ℕ-Booleω)
    SD-freeBA-ℕ = sd freeBA-ℕ-Booleω

    decPred→elem' : (Sp freeBA-ℕ-Booleω → Bool) → ⟨ freeBA ℕ ⟩
    decPred→elem' = invEq (_ , SD-freeBA-ℕ)

    decPred→elem-property' : (g : Sp freeBA-ℕ-Booleω → Bool) (h : Sp freeBA-ℕ-Booleω)
      → evaluationMap freeBA-ℕ-Booleω (decPred→elem' g) h ≡ g h
    decPred→elem-property' g h = funExt⁻ (secEq (_ , SD-freeBA-ℕ) g) h

    ¬WLPO : ¬ WLPO
    ¬WLPO wlpo = contradiction'
      where
      decide-fn : binarySequence → Bool
      decide-fn α with wlpo α
      ... | yes _ = false
      ... | no _ = true

      WLPOf : (α : binarySequence) → (decide-fn α ≡ false) ↔ ((n : ℕ) → α n ≡ false)
      WLPOf α = forward , backward
        where
        forward : decide-fn α ≡ false → (n : ℕ) → α n ≡ false
        forward fα=false with wlpo α
        ... | yes all-zero = all-zero
        ... | no _ = ex-falso (true≢false fα=false)

        backward : ((n : ℕ) → α n ≡ false) → decide-fn α ≡ false
        backward all-zero with wlpo α
        ... | yes _ = refl
        ... | no ¬all-zero = ex-falso (¬all-zero all-zero)

      elem-c : ⟨ freeBA ℕ ⟩
      elem-c = decPred→elem' (decide-fn ∘ Iso.fun Sp-freeBA-ℕ-Iso)

      SD-property : (α : binarySequence) → decide-fn α ≡ WLPOmod.evaluate α $cr elem-c
      SD-property α = sym (
        evaluationMap freeBA-ℕ-Booleω elem-c (Iso.inv Sp-freeBA-ℕ-Iso α)
          ≡⟨ decPred→elem-property' (decide-fn ∘ Iso.fun Sp-freeBA-ℕ-Iso) (Iso.inv Sp-freeBA-ℕ-Iso α) ⟩
        decide-fn (Iso.fun Sp-freeBA-ℕ-Iso (Iso.inv Sp-freeBA-ℕ-Iso α))
          ≡⟨ cong decide-fn (Iso.sec Sp-freeBA-ℕ-Iso α) ⟩
        decide-fn α ∎)

      open WLPOmod.PlayingWithWLPO' decide-fn WLPOf elem-c SD-property
