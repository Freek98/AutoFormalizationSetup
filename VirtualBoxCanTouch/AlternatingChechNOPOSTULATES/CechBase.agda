{-# OPTIONS --cubical --guardedness --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.AbGroup
open import Cubical.Functions.Surjection
open import Trichotomy

module CechBase
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
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; injSuc)
open import Cubical.Data.Fin.Base using (Fin ; fzero ; fsuc)
open import Cubical.Data.Nat.Order.Inductive using (_<ᵗ_ ; isProp<ᵗ)
open import Cubical.Data.Int.Base using (ℤ ; pos ; negsuc)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit* ; tt* ; isPropUnit*)

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.ZAction

open IsStrictTotalOrder isSTO public

-- ============================================================
-- Basic definitions
-- ============================================================

Fiber : X → Type ℓ
Fiber x = Σ[ s ∈ S ] q s ≡ x

Tuple : ℕ → X → Type ℓ
Tuple n x = Fin (suc n) → Fiber x

Ax : (x : X) → Type ℓ
Ax x = ⟨ A x ⟩

module Gx (x : X) = AbGroupStr (str (A x))

_ℤ·_ : {x : X} → ℤ → Ax x → Ax x
_ℤ·_ {x} n a = n ℤ[ AbGroup→Group (A x) ]· a

Cochain : ℕ → Type ℓ
Cochain n = (x : X) → Tuple n x → Ax x

-- Sum over Fin m in the abelian group at x
sumFin : {x : X} → (m : ℕ) → (Fin m → Ax x) → Ax x
sumFin {x} zero _ = Gx.0g x
sumFin {x} (suc m) f = Gx._+_ x (f fzero) (sumFin m (f ∘ fsuc))

-- ============================================================
-- Weak ordering on S (negation of strict)
-- ============================================================

_≤S_ : S → S → Type ℓ
a ≤S b = ¬ (b <S a)

-- ============================================================
-- Ordering predicates on tuples
-- ============================================================

-- Strict ordering: s₀ < s₁ < ⋯ < sₙ
IsStrictlyOrdered : {n : ℕ} {x : X} → Tuple n x → Type ℓ
IsStrictlyOrdered {n = zero} _ = Unit*
IsStrictlyOrdered {n = suc n} t =
  (fst (t fzero) <S fst (t (fsuc fzero))) ×
  IsStrictlyOrdered {n = n} (t ∘ fsuc)

-- Weak ordering: s₀ ≤ s₁ ≤ ⋯ ≤ sₙ
IsWeaklyOrdered : {n : ℕ} {x : X} → Tuple n x → Type ℓ
IsWeaklyOrdered {n = zero} _ = Unit*
IsWeaklyOrdered {n = suc n} t =
  (fst (t fzero) ≤S fst (t (fsuc fzero))) ×
  IsWeaklyOrdered {n = n} (t ∘ fsuc)

-- ============================================================
-- Cochain types
-- ============================================================

OrdTuple : ℕ → X → Type ℓ
OrdTuple n x = Σ[ t ∈ Tuple n x ] IsStrictlyOrdered t

OrdCochain : ℕ → Type ℓ
OrdCochain n = (x : X) → OrdTuple n x → Ax x

SemiOrdTuple : ℕ → X → Type ℓ
SemiOrdTuple n x = Σ[ t ∈ Tuple n x ] IsWeaklyOrdered t

SemiOrdCochain : ℕ → Type ℓ
SemiOrdCochain n = (x : X) → SemiOrdTuple n x → Ax x

-- ============================================================
-- Maps between complexes (trivial restrictions)
-- ============================================================

-- Restriction: standard → ordered (the π map)
π : {n : ℕ} → Cochain n → OrdCochain n
π α x (t , _) = α x t

-- Restriction: standard → semi-ordered
πsemi : {n : ℕ} → Cochain n → SemiOrdCochain n
πsemi α x (t , _) = α x t

-- ============================================================
-- Trichotomy on fibers and decidable equality
-- ============================================================

_<F_ : {x : X} → Fiber x → Fiber x → Type ℓ
(s₁ , _) <F (s₂ , _) = s₁ <S s₂

triF : {x : X} → (a b : Fiber x) → Tri (a <F b) (fst a ≡ fst b) (b <F a)
triF (s₁ , _) (s₂ , _) = is-tri s₁ s₂

decEqS : (a b : S) → Dec (a ≡ b)
decEqS a b with is-tri a b
... | tri< _ ¬p _ = no ¬p
... | tri≡ _ p _  = yes p
... | tri> _ ¬p _ = no ¬p

-- ============================================================
-- Fin utilities
-- ============================================================

Fin≡ : {m : ℕ} {a b : Fin m} → fst a ≡ fst b → a ≡ b
Fin≡ p = ΣPathP (p , isProp→PathP (λ _ → isProp<ᵗ) _ _)

fsuc-inj : {m : ℕ} {a b : Fin m} → fsuc a ≡ fsuc b → a ≡ b
fsuc-inj {m} {a} {b} p = ΣPathP (injSuc (cong fst p) , isProp→PathP (λ i → isProp<ᵗ) _ _)

-- ============================================================
-- Parity and sign (shared across modules)
-- ============================================================

parityℕ : ℕ → Bool
parityℕ zero = true
parityℕ (suc zero) = false
parityℕ (suc (suc n)) = parityℕ n

signℤ : ℕ → ℤ
signℤ n with parityℕ n
... | true  = pos 1
... | false = negsuc 0
