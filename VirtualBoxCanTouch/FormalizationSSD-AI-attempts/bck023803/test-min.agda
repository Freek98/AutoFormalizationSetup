{-# OPTIONS --cubical --guardedness #-}
module work.test-min where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Sequence using (Sequence)
open import Cubical.HITs.SequentialColimit using (SeqColim; incl; push)
open Sequence

-- Test: just sh and pc
module _ (S' : Sequence ℓ-zero) where
  sh : (k : ℕ) {n : ℕ} → obj S' n → obj S' (k + n)
  sh zero x = x
  sh (suc k) x = map S' (sh k x)

  -- Version 1: push without annotation (causes metas)
  -- pc : (k : ℕ) {n : ℕ} (x : obj S' n) → incl x ≡ incl (sh k x)
  -- pc zero x = refl
  -- pc (suc k) x = pc k x ∙ push (sh k x)

  -- Version 2: with explicit type on push result
  pc : (k : ℕ) {n : ℕ} (x : obj S' n) → Path (SeqColim S') (incl x) (incl (sh k x))
  pc zero x = refl
  pc (suc k) x = pc k x ∙ push (sh k x)
