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

open import BasicDefinitions using (binarySequence ; δSequence)
open import Parity
open import CountablyPresentedBooleanRings.Examples.NFinCofin
open DefinitionFinCofin
open NFinCofinPresentation using (singleton)
open import BooleanRing.ProductBA using (_×BR_ ; induceProdMapBR)

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

-- the two halves as Boolean-algebra homs ℕfinCofinBA → ℕfinCofinBA
--   evenHom : I ↦ I₀ = {k | 2k   ∈ I}     oddHom : I ↦ I₁ = {k | 2k+1 ∈ I}
evenHom : BoolHom ℕfinCofinBA ℕfinCofinBA
fst evenHom (α , w) = evenPart α , evenPart-FC α w
snd evenHom = makeIsCommRingHom (FC≡ refl) (λ _ _ → FC≡ refl) (λ _ _ → FC≡ refl)

oddHom : BoolHom ℕfinCofinBA ℕfinCofinBA
fst oddHom (α , w) = oddPart α , oddPart-FC α w
snd oddHom = makeIsCommRingHom (FC≡ refl) (λ _ _ → FC≡ refl) (λ _ _ → FC≡ refl)

-- the split map is now literally the universal product map of its two halves
-- (I ↦ (I₀ , I₁)).  Realizes the old `splitFun`, now for free from the product.
splitHom : BoolHom ℕfinCofinBA (ℕfinCofinBA ×BR ℕfinCofinBA)
splitHom = induceProdMapBR evenHom oddHom

-- sends a finite set to a pair of finite sets
splitHom-finite : (α : binarySequence) → isFinite α
  → isFinite (evenPart α) × isFinite (oddPart α)
splitHom-finite α fin = evenPart-fin α fin , oddPart-fin α fin

-- sends a cofinite set to a pair of cofinite sets
splitHom-cofinite : (α : binarySequence) → isCofinite α
  → isCofinite (evenPart α) × isCofinite (oddPart α)
splitHom-cofinite α cof = evenPart-cofin α cof , oddPart-cofin α cof

-- if both halves of S are empty, so is S (every n is even or odd)
seq-from-halves : (α : binarySequence)
  → evenPart α ≡ 𝟘 → oddPart α ≡ 𝟘 → α ≡ 𝟘
seq-from-halves α e o = funExt λ n → help n (even-or-odd n)
  where
    help : (n : ℕ) → Even n ⊎ Odd n → α n ≡ false
    help n (inl (k , n≡2k  )) = cong α n≡2k ∙ funExt⁻ e k
    help n (inr (k , n≡2k+1)) = cong α n≡2k+1 ∙ funExt⁻ o k

splitHom-kernel : (b : ⟨ ℕfinCofinBA ⟩) → splitHom $cr b ≡ 𝟘 → b ≡ 𝟘
splitHom-kernel (a , _) fa=0 = Σ≡Prop isPropisFiniteOrCofinite
  (seq-from-halves a (cong (λ z → fst (fst z)) fa=0) (cong (λ z → fst (snd z)) fa=0))

-- ───────────────────────────────────────────────────────────────
-- Read-off lemmas: each half kills the wrong-parity singletons.
-- `evenHom` sends odd singletons to 𝟘, `oddHom` sends even singletons to 𝟘.
-- This is exactly what the LLPO fibre argument needs: a point arriving through
-- `Sp evenHom` (resp. `Sp oddHom`) vanishes on every odd (resp. even) coordinate.
-- ───────────────────────────────────────────────────────────────
private
  𝟘fc : ⟨ ℕfinCofinBA ⟩
  𝟘fc = BooleanRingStr.𝟘 (snd ℕfinCofinBA)

even-≡ᵇ-odd : (k j : ℕ) → (double k ≡ᵇ suc (double j)) ≡ false
even-≡ᵇ-odd zero j = refl
even-≡ᵇ-odd (suc k) zero = refl
even-≡ᵇ-odd (suc k) (suc j) = even-≡ᵇ-odd k j

odd-≡ᵇ-even : (k j : ℕ) → (suc (double k) ≡ᵇ double j) ≡ false
odd-≡ᵇ-even k zero = refl
odd-≡ᵇ-even zero (suc j) = refl
odd-≡ᵇ-even (suc k) (suc j) = odd-≡ᵇ-even k j

evenPart-δ-odd : (k : ℕ) → evenPart (δSequence (suc (double k))) ≡ (λ _ → false)
evenPart-δ-odd k = funExt λ j → odd-≡ᵇ-even k j
oddPart-δ-even : (k : ℕ) → oddPart (δSequence (double k)) ≡ (λ _ → false)
oddPart-δ-even k = funExt λ j → even-≡ᵇ-odd k j

evenHom-sing-odd : (k : ℕ) → evenHom $cr singleton (suc (double k)) ≡ 𝟘fc
evenHom-sing-odd k = FC≡ (evenPart-δ-odd k)
oddHom-sing-even : (k : ℕ) → oddHom $cr singleton (double k) ≡ 𝟘fc
oddHom-sing-even k = FC≡ (oddPart-δ-even k)
