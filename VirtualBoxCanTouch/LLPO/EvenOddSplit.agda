{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module EvenOddSplit where

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import Cubical.Data.Sum

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing

open import BasicDefinitions using (binarySequence)
open import Parity
open import CountablyPresentedBooleanRings.Examples.NFinCofin
open DefinitionFinCofin
open import BooleanRing.ProductBA using (_×BR_)

-- pointwise Boolean-algebra structure on sequences (so `¬` is pointwise not,
-- matching the `¬` used in `isCofinite`)
open BooleanAlgebraStr ⦃...⦄
open BooleanRingStr ⦃...⦄
instance
  _ = booleanStructureOnBinarySequences
  _ = snd $ ℕfinCofinBA
  _ = snd $ ℕfinCofinBA ×BR ℕfinCofinBA

evenPart : binarySequence → binarySequence
evenPart α k = α (double k)

oddPart : binarySequence → binarySequence
oddPart α k = α (suc (double k))

-- ───────────────────────────────────────────────────────────────
-- Both halves preserve finiteness, cofiniteness, hence isFiniteOrCofinite
-- ───────────────────────────────────────────────────────────────
k≤double : (k : ℕ) → k ≤ double k
k≤double k = k , sym (double≡+self k)

evenPart-zeroFrom : (α : binarySequence) (n : ℕ) → isZeroFrom n α → isZeroFrom n (evenPart α)
evenPart-zeroFrom α n z k k≥n = z (double k) (≤-trans k≥n (k≤double k))

oddPart-zeroFrom : (α : binarySequence) (n : ℕ) → isZeroFrom n α → isZeroFrom n (oddPart α)
oddPart-zeroFrom α n z k k≥n = z (suc (double k)) (≤-trans k≥n (≤-trans (k≤double k) (≤-suc ≤-refl)))

evenPart-fin : (α : binarySequence) → isFinite α → isFinite (evenPart α)
evenPart-fin α fin = let (n , z) = finite→Bounded α fin
                     in bounded→Finite (evenPart α) n (evenPart-zeroFrom α n z)

oddPart-fin : (α : binarySequence) → isFinite α → isFinite (oddPart α)
oddPart-fin α fin = let (n , z) = finite→Bounded α fin
                    in bounded→Finite (oddPart α) n (oddPart-zeroFrom α n z)

evenPart-¬ : (α : binarySequence) → evenPart (¬ α) ≡ ¬ (evenPart α)
evenPart-¬ α = refl
oddPart-¬ : (α : binarySequence) → oddPart (¬ α) ≡ ¬ (oddPart α)
oddPart-¬ α = refl

evenPart-cofin : (α : binarySequence) → isCofinite α → isCofinite (evenPart α)
evenPart-cofin α cof = subst isFinite (sym (evenPart-¬ α)) (evenPart-fin (¬ α) cof)
oddPart-cofin : (α : binarySequence) → isCofinite α → isCofinite (oddPart α)
oddPart-cofin α cof = subst isFinite (sym (oddPart-¬ α)) (oddPart-fin (¬ α) cof)

evenPart-FC : (α : binarySequence) → isFiniteOrCofinite α → isFiniteOrCofinite (evenPart α)
evenPart-FC α (Fin f) = Fin (evenPart-fin α f)
evenPart-FC α (Cof c) = Cof (evenPart-cofin α c)
oddPart-FC : (α : binarySequence) → isFiniteOrCofinite α → isFiniteOrCofinite (oddPart α)
oddPart-FC α (Fin f) = Fin (oddPart-fin α f)
oddPart-FC α (Cof c) = Cof (oddPart-cofin α c)

-- ───────────────────────────────────────────────────────────────
-- The split map and its trivial kernel
-- ───────────────────────────────────────────────────────────────

-- the underlying function: I ↦ (I₀ , I₁), with I₀ = {k | 2k ∈ I}, I₁ = {k | 2k+1 ∈ I}
-- This should also exist by universal property of the product. 
splitFun : ⟨ ℕfinCofinBA ⟩ → ⟨ ℕfinCofinBA ×BR ℕfinCofinBA ⟩
splitFun (α , w) = (evenPart α , evenPart-FC α w) , (oddPart α , oddPart-FC α w)

splitHom : BoolHom ℕfinCofinBA (ℕfinCofinBA ×BR ℕfinCofinBA)
fst splitHom = splitFun
snd splitHom = makeIsCommRingHom
  (cong₂ _,_ (FC≡ refl) (FC≡ refl))
  (λ { (α , w) (β , w') → cong₂ _,_ (FC≡ refl) (FC≡ refl) })
  (λ { (α , w) (β , w') → cong₂ _,_ (FC≡ refl) (FC≡ refl) })

-- sends a finite set to a pair of finite sets
splitHom-finite : (α : binarySequence) → isFinite α
  → isFinite (evenPart α) × isFinite (oddPart α)
splitHom-finite α fin = evenPart-fin α fin , oddPart-fin α fin

-- sends a cofinite set to a pair of cofinite sets
splitHom-cofinite : (α : binarySequence) → isCofinite α
  → isCofinite (evenPart α) × isCofinite (oddPart α)
splitHom-cofinite α cof = evenPart-cofin α cof , oddPart-cofin α cof

-- if both halves of S are empty, so is S (every n is even or odd)
-- This seems actually like two proofs of injectivity. 
seq-from-halves : (α : binarySequence)
  → evenPart α ≡ 𝟘 → oddPart α ≡ 𝟘 → α ≡ 𝟘
seq-from-halves α e o = funExt λ n → help n (even-or-odd n)
  where
    help : (n : ℕ) → Even n ⊎ Odd n → α n ≡ false
    help n (inl (k , n≡2k)) = cong α n≡2k ∙ funExt⁻ e k
    help n (inr (k , n≡2k+1)) = cong α n≡2k+1 ∙ funExt⁻ o k

-- the kernel is trivial: splitHom S = (∅ , ∅) ⇒ S = ∅
splitHom-kernel : (b : ⟨ ℕfinCofinBA ⟩) → splitHom $cr b ≡ 𝟘 → b ≡ 𝟘
splitHom-kernel (a , _) fa=0 = Σ≡Prop isPropisFiniteOrCofinite
  (seq-from-halves a (cong (λ z → fst (fst z)) fa=0) (cong (λ z → fst (snd z)) fa=0))
