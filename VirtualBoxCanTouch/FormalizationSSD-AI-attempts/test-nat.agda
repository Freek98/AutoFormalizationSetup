{-# OPTIONS --cubical --guardedness #-}
module test-nat where
open import Cubical.Data.Nat.Base
open import Cubical.Foundations.Prelude

test : (n : ℕ) → n + 0 ≡ n
test n = refl
