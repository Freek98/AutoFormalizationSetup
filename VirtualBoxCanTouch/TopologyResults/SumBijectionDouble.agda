-- The forward map of ℕ ⊎ ℕ ≅ ℕ is the even/odd interleaving:
--   inl k  ↦  doubleℕ k        (the evens)
--   inr k  ↦  suc (doubleℕ k)  (the odds)
--
-- This is the index bookkeeping behind Interleave.combine (α on the evens, β on the
-- odds): combine's hit at `Iso.fun ℕ⊎ℕ≅ℕ (inl k)` is α k, at `... (inr k)` is β k.
--
-- Both hold definitionally: ℕ⊎ℕ≅ℕ sends inl n to the partition cell (n , 0 , _) and
-- inr n to (n , 1 , _), and partition≅ℕ reads (k , i , _) off as `i + doubleℕ k`,
-- so `0 + doubleℕ n ≡ doubleℕ n` and `1 + doubleℕ n ≡ suc (doubleℕ n)` are refl.
module SumBijectionDouble where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ ; suc ; doubleℕ)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)

ℕ⊎ℕ≅ℕ-fun-inl : (k : ℕ) → Iso.fun ℕ⊎ℕ≅ℕ (inl k) ≡ doubleℕ k
ℕ⊎ℕ≅ℕ-fun-inl k = refl

ℕ⊎ℕ≅ℕ-fun-inr : (k : ℕ) → Iso.fun ℕ⊎ℕ≅ℕ (inr k) ≡ suc (doubleℕ k)
ℕ⊎ℕ≅ℕ-fun-inr k = refl
