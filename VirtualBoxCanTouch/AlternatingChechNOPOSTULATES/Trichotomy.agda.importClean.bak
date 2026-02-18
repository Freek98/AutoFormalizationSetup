{-# OPTIONS --cubical --guardedness #-}

module Trichotomy where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

private variable
  ℓ ℓ' : Level

-- Three-way comparison result
data Tri {ℓa ℓb ℓc} (A : Type ℓa) (B : Type ℓb) (C : Type ℓc)
  : Type (ℓ-max ℓa (ℓ-max ℓb ℓc)) where
  tri< : A → ¬ B → ¬ C → Tri A B C
  tri≡ : ¬ A → B → ¬ C → Tri A B C
  tri> : ¬ A → ¬ B → C → Tri A B C

record IsStrictTotalOrder {ℓ ℓ' : Level} {A : Type ℓ}
  (_<_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    is-set : isSet A
    is-prop-valued : (a b : A) → isProp (a < b)
    is-irrefl : (a : A) → ¬ (a < a)
    is-trans : (a b c : A) → a < b → b < c → a < c
    is-tri : (a b : A) → Tri (a < b) (a ≡ b) (b < a)

  is-asym : (a b : A) → a < b → ¬ (b < a)
  is-asym a b a<b b<a = is-irrefl a (is-trans a b a a<b b<a)
