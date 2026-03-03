{-# OPTIONS --cubical --guardedness #-}
module test-scope where
open import work.Part06
open import Cubical.Data.Nat using (ℕ)
test : {n : ℕ} → n ≤ n
test = ≤-refl
