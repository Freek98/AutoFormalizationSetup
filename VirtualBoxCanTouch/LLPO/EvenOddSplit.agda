{-# OPTIONS --cubical --guardedness --lossy-unification #-}
-- The concrete even/odd split underlying the injectivity of the LLPO map f.
--
-- Working in the finite/cofinite model B∞ ≅ ℕfinCofinBA (binary sequences that
-- are finite or cofinite as subsets of ℕ), the map f sends a set S to the pair
-- of its "even half" and "odd half":
--     splitFC S = ( k ↦ S(2k) , k ↦ S(2k+1) ).
-- This file defines that map (`splitFC`) and proves the fact the kernel
-- argument needs: splitFC has a trivial kernel, i.e. if both halves are empty
-- then S is empty — uniformly, since every n is even or odd.  (As corollaries:
-- a cofinite S has cofinite — hence nonempty — halves, and a finite S splits to
-- a pair of empty sets exactly when S was already empty.)
--
-- It is kept in its own file so as not to interfere with the product-closure
-- work on LLPOAttemptLLMAided.agda.  The remaining step (identifying splitFC,
-- transported along the iso, with the actual f) lives with f in the main file.
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
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import BasicDefinitions using (binarySequence)
open import Parity
open import CountablyPresentedBooleanRings.Examples.NFinCofin
open DefinitionFinCofin
open import BooleanRing.ProductBA using (_×BR_)

-- pointwise Boolean-algebra structure on sequences (so `¬` is pointwise not,
-- matching the `¬` used in `isCofinite`)
instance
  _ = booleanStructureOnBinarySequences
open BooleanAlgebraStr ⦃...⦄ using (¬_)

private
  𝟘fc : ⟨ ℕfinCofinBA ⟩
  𝟘fc = BooleanRingStr.𝟘 (snd ℕfinCofinBA)
  𝟘prod : ⟨ ℕfinCofinBA ×BR ℕfinCofinBA ⟩
  𝟘prod = BooleanRingStr.𝟘 (snd (ℕfinCofinBA ×BR ℕfinCofinBA))
  -- the underlying zero sequence is `λ _ → false` (definitionally)
  _ : fst 𝟘fc ≡ (λ _ → false)
  _ = refl

-- ───────────────────────────────────────────────────────────────
-- The even/odd halves of a binary sequence
-- ───────────────────────────────────────────────────────────────

evenPart : binarySequence → binarySequence
evenPart α k = α (double k)

oddPart : binarySequence → binarySequence
oddPart α k = α (suc (double k))

k≤double : (k : ℕ) → k ≤ double k
k≤double k = k , sym (double≡+self k)

-- ───────────────────────────────────────────────────────────────
-- Both halves preserve finiteness, cofiniteness, hence isFiniteOrCofinite
-- ───────────────────────────────────────────────────────────────

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

-- the halves commute with pointwise negation
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
splitFun : ⟨ ℕfinCofinBA ⟩ → ⟨ ℕfinCofinBA ×BR ℕfinCofinBA ⟩
splitFun (α , w) = (evenPart α , evenPart-FC α w) , (oddPart α , oddPart-FC α w)

-- …and it is a Boolean-algebra map: the operations are pointwise on the sequence
-- and componentwise in the product, so each homomorphism law holds componentwise
-- and definitionally on the underlying sequences (`FC≡ refl`).
splitFC : BoolHom ℕfinCofinBA (ℕfinCofinBA ×BR ℕfinCofinBA)
fst splitFC = splitFun
snd splitFC = makeIsCommRingHom
  (cong₂ _,_ (FC≡ refl) (FC≡ refl))
  (λ { (α , w) (β , w') → cong₂ _,_ (FC≡ refl) (FC≡ refl) })
  (λ { (α , w) (β , w') → cong₂ _,_ (FC≡ refl) (FC≡ refl) })

-- sends a finite set to a pair of finite sets
splitFC-finite : (α : binarySequence) → isFinite α
  → isFinite (evenPart α) × isFinite (oddPart α)
splitFC-finite α fin = evenPart-fin α fin , oddPart-fin α fin

-- sends a cofinite set to a pair of cofinite sets
splitFC-cofinite : (α : binarySequence) → isCofinite α
  → isCofinite (evenPart α) × isCofinite (oddPart α)
splitFC-cofinite α cof = evenPart-cofin α cof , oddPart-cofin α cof

-- if both halves of S are empty, so is S (every n is even or odd)
seq-from-halves : (α : binarySequence)
  → evenPart α ≡ (λ _ → false) → oddPart α ≡ (λ _ → false) → α ≡ (λ _ → false)
seq-from-halves α e o = funExt λ n → help n (even-or-odd n)
  where
    help : (n : ℕ) → Even n ⊎ Odd n → α n ≡ false
    help n (inl (k , n≡2k)) = cong α n≡2k ∙ funExt⁻ e k
    help n (inr (k , n≡2k+1)) = cong α n≡2k+1 ∙ funExt⁻ o k

-- the kernel is trivial: splitFC S = (∅ , ∅) ⇒ S = ∅
splitFC-kernel : (a : ⟨ ℕfinCofinBA ⟩) → splitFC $cr a ≡ 𝟘prod → a ≡ 𝟘fc
splitFC-kernel (α , w) p = Σ≡Prop isPropisFiniteOrCofinite
  (seq-from-halves α (cong (λ z → fst (fst z)) p) (cong (λ z → fst (snd z)) p))
