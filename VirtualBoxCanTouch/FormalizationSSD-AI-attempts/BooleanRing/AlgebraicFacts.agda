{-# OPTIONS --cubical --guardedness #-}
module BooleanRing.AlgebraicFacts where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import BooleanRing.BooleanRingMaps
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude hiding (_∧_;_∨_)

module _ {ℓ : Level} (B : BooleanRing ℓ) where
  open BooleanRingStr (snd B)
  open BooleanAlgebraStr (snd B)
  +FromBooleanAlgebraStr : { x y : ⟨ B ⟩ } → ((x + y) ≡ ( (x ∧ (¬ y)) ∨ ((¬ x) ∧ y)))
  +FromBooleanAlgebraStr {x} {y} = sym $
    ((x ∧ (¬ y)) ∨ ((¬ x) ∧ y)) 
      ≡⟨⟩ 
    ((x ∧ (¬ y)) + ((¬ x) ∧ y)) + ((x ∧ (¬ y)) ∧ ((¬ x) ∧ y)) 
      ≡⟨ solve! (BooleanRing→CommRing B) ⟩ 
    ((x ∧ (¬ y)) + ((¬ x) ∧ y)) + ((x ∧ (¬ x)) ∧ ((¬ y) ∧ y))
      ≡⟨ cong (λ b → ((x ∧ (¬ y)) + ((¬ x) ∧ y)) + (b ∧ ((¬ y) ∧ y))) ¬Cancels∧R ⟩ 
    ((x ∧ (¬ y)) + ((¬ x) ∧ y)) + (𝟘  ∧ ((¬ y) ∧ y) )
      ≡⟨ solve! (BooleanRing→CommRing B) ⟩ 
    ((x ∧ (¬ y)) + ((¬ x) ∧ y)) 
      ≡⟨⟩ 
    ((x ∧ (𝟙 + y)) + ((𝟙 + x) ∧ y)) 
      ≡⟨ solve! (BooleanRing→CommRing B) ⟩ 
    (x + (x · y)) + ( y + x · y)
      ≡⟨ solve! (BooleanRing→CommRing B) ⟩ 
    (x + y) + (x · y + x · y) 
      ≡⟨ cong (λ b → (x + y) + b) characteristic2 ⟩ 
    (x + y) + 𝟘
      ≡⟨ +IdR (x + y) ⟩ 
    x + y ∎





