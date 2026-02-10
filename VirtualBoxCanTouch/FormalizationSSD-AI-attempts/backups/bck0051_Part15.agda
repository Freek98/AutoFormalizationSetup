{-# OPTIONS --cubical --guardedness #-}

module work.Part15 where

open import work.Part14 public

module ConnectednessForBoolILocal where
  open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

  is-1-connected : Type ℓ-zero → Type ℓ-zero
  is-1-connected A = isContr ∥ A ∥₁