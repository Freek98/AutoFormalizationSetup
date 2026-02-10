{-# OPTIONS --cubical --guardedness #-}

module work.Part10 where

open import work.Part09 public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; hProp; isProp×; isSetΣ)
open import Cubical.Foundations.Equiv using (_≃_; equivFun; invEq; secEq; retEq)
open import Cubical.Foundations.Univalence using (pathToEquiv; hPropExt)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv; isoToPath; iso)
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥) renaming (rec to ex-falso)
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum using (_⊎_; inl; inr; isProp⊎)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; elim; squash₁)
open import Cubical.Algebra.BooleanRing using (BooleanRing; BooleanRingStr; BoolHom)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.CommRing using (CommRing; CommRingHom; _∘cr_; CommRingHom≡)
open import Axioms.StoneDuality using (Booleω; Sp)

pathToEquiv' : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A ≃ B
pathToEquiv' = pathToEquiv

module StoneAsClosedSubsetOfCantorModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Foundations.Equiv using (compEquiv)
  open ClosedInStoneIsStoneModule
  open StoneClosedSubsetsModule
  open CantorIsStoneModule

  CantorStone : Stone
  CantorStone = CantorSpace , CantorIsStone

  ClosedSubsetOfCantor : Type₁
  ClosedSubsetOfCantor = Σ[ A ∈ (CantorSpace → hProp ℓ-zero) ] ((x : CantorSpace) → isClosedProp (A x))

  module Stone→ClosedInCantorProof where
    open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv)
    open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator)
    open import Axioms.StoneDuality using (SpGeneralBooleanRing)
    import QuotientBool as QB
    open StoneClosedSubsetsModule.SpOfQuotientBySeq
    import Cubical.Foundations.Equiv as Eq
    open Eq using (compEquiv)

    Stone→Closed-from-pres : (B : BooleanRing ℓ-zero)
      → (pres : has-Boole-ω' B)
      → Σ[ A ∈ ClosedSubsetOfCantor ] (Sp (B , ∣ pres ∣₁) ≃ (Σ[ x ∈ CantorSpace ] fst (fst A x)))

    Stone→Closed-from-pres B (f , equiv) = (A , A-closed) , SpB≃ΣA
      where
      Q : BooleanRing ℓ-zero
      Q = freeBA ℕ QB./Im f

      B≃Q : ⟨ B ⟩ ≃ ⟨ Q ⟩
      B≃Q = fst equiv

      Sp-to-Cantor : SpGeneralBooleanRing (freeBA ℕ) → CantorSpace
      Sp-to-Cantor = Iso.fun Sp-freeBA-ℕ-Iso

      Cantor-to-Sp : CantorSpace → SpGeneralBooleanRing (freeBA ℕ)
      Cantor-to-Sp = Iso.inv Sp-freeBA-ℕ-Iso

      A-pred : CantorSpace → Type ℓ-zero
      A-pred α = (n : ℕ) → fst (Cantor-to-Sp α) (f n) ≡ false

      A-isProp : (α : CantorSpace) → isProp (A-pred α)
      A-isProp α = isPropΠ (λ n → isSetBool _ _)

      A : CantorSpace → hProp ℓ-zero
      A α = A-pred α , A-isProp α

      A-closed : (α : CantorSpace) → isClosedProp (A α)
      A-closed α = closedCountableIntersection P P-closed
        where
        h : SpGeneralBooleanRing (freeBA ℕ)
        h = Cantor-to-Sp α

        P : ℕ → hProp ℓ-zero
        P n = (fst h (f n) ≡ false) , isSetBool _ _

        P-closed : (n : ℕ) → isClosedProp (P n)
        P-closed n = StoneEqualityClosedModule.Bool-eq-closed (fst h (f n)) false

      module SQS = SpOfQuotientBySeq (freeBA ℕ) f

      SpQ≃ClosedSubsetSp : BoolHom Q BoolBR ≃ SQS.ClosedSubset
      SpQ≃ClosedSubsetSp = SQS.Sp-quotient-≃

      Sp-freeBA-ℕ-≃ : SpGeneralBooleanRing (freeBA ℕ) ≃ CantorSpace
      Sp-freeBA-ℕ-≃ = isoToEquiv Sp-freeBA-ℕ-Iso

      Cantor-Sp-roundtrip : (h : SpGeneralBooleanRing (freeBA ℕ)) → Cantor-to-Sp (Sp-to-Cantor h) ≡ h
      Cantor-Sp-roundtrip h = Iso.ret Sp-freeBA-ℕ-Iso h

      fiber-transport : (h : SpGeneralBooleanRing (freeBA ℕ))
        → ((n : ℕ) → fst h (f n) ≡ false)
        ≃ ((n : ℕ) → fst (Cantor-to-Sp (Sp-to-Cantor h)) (f n) ≡ false)
      fiber-transport h = pathToEquiv' (cong (λ h' → (n : ℕ) → fst h' (f n) ≡ false) (sym (Cantor-Sp-roundtrip h)))

      ClosedSubsetSp≃ΣA : SQS.ClosedSubset ≃ (Σ[ α ∈ CantorSpace ] fst (A α))
      ClosedSubsetSp≃ΣA = Σ-cong-equiv Sp-freeBA-ℕ-≃ fiber-transport

      SpQ≃ΣA : BoolHom Q BoolBR ≃ (Σ[ α ∈ CantorSpace ] fst (A α))
      SpQ≃ΣA = compEquiv SpQ≃ClosedSubsetSp ClosedSubsetSp≃ΣA

      open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanEquivToHomInv)

      equiv-inv-hom : BoolHom Q B
      equiv-inv-hom = BooleanEquivToHomInv B Q equiv

      SpB≃SpQ : Sp (B , ∣ (f , equiv) ∣₁) ≃ BoolHom Q BoolBR
      SpB≃SpQ = isoToEquiv SpB-SpQ-Iso
        where
        forward : BoolHom B BoolBR → BoolHom Q BoolBR
        forward h = h ∘cr equiv-inv-hom

        equiv-hom : BoolHom B Q
        equiv-hom = fst B≃Q , snd equiv

        backward : BoolHom Q BoolBR → BoolHom B BoolBR
        backward k = k ∘cr equiv-hom

        fwd∘bwd : (k : BoolHom Q BoolBR) → forward (backward k) ≡ k
        fwd∘bwd k = CommRingHom≡ (funExt λ q →
          cong (fst k) (secEq B≃Q q))

        bwd∘fwd : (h : BoolHom B BoolBR) → backward (forward h) ≡ h
        bwd∘fwd h = CommRingHom≡ (funExt λ b →
          cong (fst h) (retEq B≃Q b))

        SpB-SpQ-Iso : Iso (BoolHom B BoolBR) (BoolHom Q BoolBR)
        Iso.fun SpB-SpQ-Iso = forward
        Iso.inv SpB-SpQ-Iso = backward
        Iso.sec SpB-SpQ-Iso = fwd∘bwd
        Iso.ret SpB-SpQ-Iso = bwd∘fwd

      SpB≃ΣA : Sp (B , ∣ (f , equiv) ∣₁) ≃ (Σ[ α ∈ CantorSpace ] fst (A α))
      SpB≃ΣA = compEquiv SpB≃SpQ SpQ≃ΣA

    Stone→ClosedInCantor : (S : Stone)
      → ∥ Σ[ A ∈ ClosedSubsetOfCantor ] (fst S ≃ (Σ[ x ∈ CantorSpace ] fst (fst A x))) ∥₁
    Stone→ClosedInCantor (|S| , ((B , trunc-pres) , SpB≡S)) =
      PT.rec squash₁ go trunc-pres
      where
      go : has-Boole-ω' B → ∥ Σ[ A ∈ ClosedSubsetOfCantor ] (|S| ≃ (Σ[ α ∈ CantorSpace ] fst (fst A α))) ∥₁
      go pres = ∣ fst (Stone→Closed-from-pres B pres) ,
                  compEquiv (pathToEquiv (sym SpB≡S)) (snd (Stone→Closed-from-pres B pres)) ∣₁

  open Stone→ClosedInCantorProof using (Stone→ClosedInCantor) public

  ClosedInCantor→Stone : (A : ClosedSubsetOfCantor)
    → hasStoneStr (Σ[ x ∈ CantorSpace ] (fst (fst A x)))
  ClosedInCantor→Stone (A , Aclosed) = ClosedInStoneIsStone CantorStone A Aclosed
