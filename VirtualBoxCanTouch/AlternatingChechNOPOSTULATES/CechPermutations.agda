{-# OPTIONS --cubical --guardedness --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.AbGroup
open import Cubical.Functions.Surjection
open import Trichotomy

module CechPermutations
  {ℓ : Level}
  {S : Type ℓ}
  {X : Type ℓ}
  (_<S_ : S → S → Type ℓ)
  (isSTO : IsStrictTotalOrder _<S_)
  (isSetX : isSet X)
  (q : S → X)
  (isSurjQ : isSurjection q)
  (A : X → AbGroup ℓ)
  where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Base using (Fin ; fzero ; fsuc)
open import Cubical.Data.Nat.Order.Inductive using (<→<ᵗ)
open import Cubical.Data.Int.Base using (ℤ ; pos ; negsuc)
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary

open import CechBase _<S_ isSTO isSetX q isSurjQ A

-- ============================================================
-- Permutations and sign
-- ============================================================

Perm : ℕ → Type₀
Perm m = Fin m ≃ Fin m

idPerm : {m : ℕ} → Perm m
idPerm = idEquiv (Fin _)

applyPerm : {n : ℕ} {x : X} → Perm (suc n) → Tuple n x → Tuple n x
applyPerm σ t = t ∘ equivFun σ

-- Count inversions of a sequence f(0), f(1), ..., f(m-1)
invCountℕ : (m : ℕ) → (ℕ → ℕ) → ℕ
invCountℕ zero _ = zero
invCountℕ (suc m) f = headInv m + invCountℕ m (f ∘ suc)
  where
  headInv : ℕ → ℕ
  headInv zero = zero
  headInv (suc k) with f zero ≟ f (suc k)
  ... | gt _ = suc (headInv k)
  ... | _    = headInv k

-- Extract the underlying ℕ→ℕ function from a Fin permutation
permToℕFun : {m : ℕ} → Perm m → ℕ → ℕ
permToℕFun {zero} _ k = k
permToℕFun {suc m} σ k with k ≟ suc m
... | lt p = fst (equivFun σ (k , <→<ᵗ p))
... | eq _ = k
... | gt _ = k

-- Sign of a permutation: (-1)^(number of inversions)
sgnPerm : {m : ℕ} → Perm m → ℤ
sgnPerm {m} σ with parityℕ (invCountℕ m (permToℕFun σ))
... | true  = pos 1
... | false = negsuc 0

-- ============================================================
-- Repeats, alternating condition, vanishes on repeats
-- ============================================================

HasRepeat : {n : ℕ} {x : X} → Tuple n x → Type ℓ
HasRepeat {n} t = Σ[ i ∈ Fin (suc n) ] Σ[ j ∈ Fin (suc n) ]
  (¬ (i ≡ j)) × (fst (t i) ≡ fst (t j))

IsAlternating : {n : ℕ} → Cochain n → Type ℓ
IsAlternating {n} α =
  (x : X) (σ : Perm (suc n)) (t : Tuple n x) →
    α x (applyPerm σ t) ≡ (sgnPerm σ) ℤ· (α x t)

VanishesOnRepeats : {n : ℕ} → Cochain n → Type ℓ
VanishesOnRepeats {n} α =
  (x : X) (t : Tuple n x) → HasRepeat t → α x t ≡ Gx.0g x

-- ============================================================
-- Alternating and semi-alternating cochain types
-- ============================================================

AltCochain : ℕ → Type ℓ
AltCochain n = Σ[ α ∈ Cochain n ] IsAlternating α

SemiAltCochain : ℕ → Type ℓ
SemiAltCochain n = Σ[ α ∈ Cochain n ] VanishesOnRepeats α

-- Inclusion: alternating → standard
altIncl : {n : ℕ} → AltCochain n → Cochain n
altIncl = fst
