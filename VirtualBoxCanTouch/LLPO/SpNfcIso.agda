{-# OPTIONS --cubical --guardedness --lossy-unification #-}
-- The Stone iso for the finite/cofinite model: Sp(ℕfinCofinBA) ≅ ℕ∞.
--
-- This is the `neededIso` analogue built directly from ℕfinCofinBA's universal
-- property (`extensionMap`/`extensionCommutes`/`extensionUnique` of NFinCofin),
-- with `fun` reading a point off as its values on the singleton generators —
-- exactly the `toℕ∞seq` of SplitNaturality.  It lets the spectrum action of
-- splitFC be transported to ℕ∞ ⊎ ℕ∞ → ℕ∞.
module SpNfcIso where

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma hiding (_∧_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import BasicDefinitions using (binarySequence ; δSequence)
open import BooleanRing.BooleanRingMaps
open import BooleanRing.FreeBooleanRing.FreeBool
open import StoneSpaces.Spectrum using (SpGeneralBooleanRing)
open import CountablyPresentedBooleanRings.Examples.NFinCofin
open NFinCofinPresentation
  using (singleton ; extensionMap ; extensionCommutes ; extensionUnique
        ; eval-gen ; freeℕ→ℕFinCof ; δn∧δm=0)
open import NinftyExtras
  using (ℕ∞ ; hits1AtMostOnce ; isPropHits1AtMostOnce
        ; BinarySequence→SpFreeℕ ; hits1AtMostOnce→respectsRelations)
open import SplitNaturality using (toℕ∞seq)

private
  𝟘fc : ⟨ ℕfinCofinBA ⟩
  𝟘fc = BooleanRingStr.𝟘 (snd ℕfinCofinBA)

-- orthogonality of singletons in ℕfinCofinBA
sing·0 : (n m : ℕ) → (n ≡ m → ⊥) → BooleanRingStr._·_ (snd ℕfinCofinBA) (singleton n) (singleton m) ≡ 𝟘fc
sing·0 n m n≠m = FC≡ (funExt (δn∧δm=0 n m n≠m))

-- a point hits 1 at most once: its values on distinct singletons can't both be 1
atMostOnce : (γ : SpGeneralBooleanRing ℕfinCofinBA) → hits1AtMostOnce (toℕ∞seq γ)
atMostOnce γ n m γn=1 γm=1 with discreteℕ n m
... | yes p = p
... | no n≠m = ex-falso (true≢false
      ( sym (cong₂ _and_ γn=1 γm=1)
      ∙ sym (IsCommRingHom.pres· (snd γ) (singleton n) (singleton m))
      ∙ cong (fst γ) (sing·0 n m n≠m)
      ∙ IsCommRingHom.pres0 (snd γ) ))

-- the relations of the presentation are respected by a point's free extension
relproof : (α : binarySequence) → hits1AtMostOnce α
  → (n : ℕ) → BinarySequence→SpFreeℕ α $cr relationsℕ n ≡ BooleanRingStr.𝟘 (snd BoolBR)
relproof α α1 n = hits1AtMostOnce→respectsRelations α α1
  (fst (Iso.inv ℕ×ℕ≅ℕ n)) (snd (Iso.inv ℕ×ℕ≅ℕ n))

σ : Iso (SpGeneralBooleanRing ℕfinCofinBA) ℕ∞
σ .Iso.fun γ = toℕ∞seq γ , atMostOnce γ
σ .Iso.inv (α , α1) = extensionMap BoolBR (BinarySequence→SpFreeℕ α) (relproof α α1)
σ .Iso.sec (α , α1) = Σ≡Prop isPropHits1AtMostOnce (funExt secAt)
  where
    secAt : (n : ℕ) → toℕ∞seq (σ .Iso.inv (α , α1)) n ≡ α n
    secAt n =
      σ .Iso.inv (α , α1) $cr singleton n
        ≡⟨ cong (λ s → σ .Iso.inv (α , α1) $cr s) (sym (eval-gen n)) ⟩
      σ .Iso.inv (α , α1) $cr (freeℕ→ℕFinCof $cr generator n)
        ≡⟨ cong (λ h → h $cr generator n)
                (extensionCommutes BoolBR (BinarySequence→SpFreeℕ α) (relproof α α1)) ⟩
      BinarySequence→SpFreeℕ α $cr generator n
        ≡⟨ funExt⁻ (evalBAInduce ℕ BoolBR α) n ⟩
      α n ∎
σ .Iso.ret γ =
  extensionUnique BoolBR (BinarySequence→SpFreeℕ (toℕ∞seq γ)) (relproof (toℕ∞seq γ) (atMostOnce γ)) γ
    (inducedBAHomUnique ℕ BoolBR (toℕ∞seq γ) (γ ∘cr freeℕ→ℕFinCof)
      (funExt λ n → cong (fst γ) (eval-gen n)))
