{-# OPTIONS --cubical --guardedness --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.AbGroup
open import Cubical.Functions.Surjection
open import Trichotomy

module CechFaceMaps
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

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Base using (Fin ; fzero ; fsuc)
open import Cubical.Data.Nat.Order.Inductive using (_<ᵗ_ ; <ᵗ-trans-suc ; isProp<ᵗ)
open import Cubical.Data.Int.Base using (ℤ ; pos ; negsuc)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit* ; tt ; tt*)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.ZAction

open import CechBase _<S_ isSTO isSetX q isSurjQ A

-- ============================================================
-- Skip index and face maps
-- ============================================================

-- Skip index: maps Fin (n+1) → Fin (n+2) skipping position i
skip : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n) → Fin (suc (suc n))
skip (zero , _) (j , jp) = (suc j , jp)
skip (suc _ , _) (zero , _) = (zero , tt)
skip {suc n} (suc i , ip) (suc j , jp) = fsuc (skip {n} (i , ip) (j , jp))

-- Face map: delete position i from an (n+2)-tuple
face : {n : ℕ} {x : X} → Fin (suc (suc n)) → Tuple (suc n) x → Tuple n x
face i t = t ∘ skip i

-- Standard Cech differential
cechDiff : {n : ℕ} → Cochain n → Cochain (suc n)
cechDiff {n} α x t = sumFin (suc (suc n)) term
  where
  term : Fin (suc (suc n)) → Ax x
  term i = (signℤ (fst i)) ℤ· (α x (face i t))

-- ============================================================
-- Face maps preserve strict ordering
-- ============================================================

face-preserves-strict : {n : ℕ} {x : X}
  → (i : Fin (suc (suc n))) → (t : Tuple (suc n) x)
  → IsStrictlyOrdered t → IsStrictlyOrdered (face i t)
face-preserves-strict {zero} i t ord = tt*
face-preserves-strict {suc n} (zero , p) t ord = snd ord
face-preserves-strict {suc n} (suc zero , p) t (h< , rest) =
  is-trans _ _ _ h< (fst rest) , face-preserves-strict (zero , tt) (t ∘ fsuc) rest
face-preserves-strict {suc n} (suc (suc k) , p) t (h< , rest) =
  h< , face-preserves-strict (suc k , p) (t ∘ fsuc) rest

-- Ordered differential
ordDiff : {n : ℕ} → OrdCochain n → OrdCochain (suc n)
ordDiff {n} α x (t , ord) = sumFin (suc (suc n)) term
  where
  term : Fin (suc (suc n)) → Ax x
  term i = (signℤ (fst i)) ℤ· α x (face i t , face-preserves-strict i t ord)

-- ============================================================
-- Simplicial identity: skip i ∘ skip j = skip (j+1) ∘ skip i  (for fst i ≤ fst j)
-- ============================================================

skip-skip : {n : ℕ} (i : Fin (suc (suc (suc n)))) (j : Fin (suc (suc n)))
  → fst i ≤ fst j
  → (ip' : fst i <ᵗ suc (suc n))
  → (k : Fin (suc n))
  → skip i (skip j k) ≡ skip (fsuc j) (skip (fst i , ip') k)
skip-skip (zero , _) _ _ _ _ = refl
skip-skip (suc _ , _) (zero , _) le _ _ = ⊥-rec (¬-<-zero le)
skip-skip (suc _ , _) (suc _ , _) _ _ (zero , _) = refl
skip-skip {suc n'} (suc a , ap) (suc b , bp) le ip' (suc c , cp) =
  cong fsuc (skip-skip (a , ap) (b , bp) (pred-≤-pred le) ip' (c , cp))
