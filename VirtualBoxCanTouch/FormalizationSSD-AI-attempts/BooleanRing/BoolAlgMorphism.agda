{-# OPTIONS --cubical --guardedness #-}
-- Note from Freek: this is exactly what I wanted from it, I think i'm changing some names, but I'm quite happy with the result. 
module BooleanRing.BoolAlgMorphism where

open import Cubical.Foundations.Prelude hiding (_∧_ ; _∨_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import BooleanRing.AlgebraicFacts

private variable ℓ ℓ' : Level

module _ (A : BooleanRing ℓ) (B : BooleanRing ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) where
  open BooleanAlgebraStr ⦃...⦄
  open BooleanRingStr ⦃...⦄
  instance 
    _ = snd A
    _ = snd B

  module FromPres¬∧
    (pres¬ : ∀ x → f (¬ x) ≡ ¬ (f x))
    (pres∧ : ∀ x y → f (x ∧ y) ≡ (f x) ∧ (f y))
    where

    pres· : ∀ x y → f (x · y) ≡ (f x) · (f y)
    pres· = pres∧

    pres0 : f 𝟘 ≡ 𝟘
    pres0 =
      f 𝟘
        ≡⟨ cong f (sym (¬Cancels∧R {x = 𝟙})) ⟩
      f (𝟙 ∧ ¬ 𝟙)
        ≡⟨ pres∧ 𝟙 (¬ 𝟙) ⟩
      (f 𝟙) ∧ f (¬ 𝟙)
        ≡⟨ cong ((f 𝟙) ∧_) (pres¬ 𝟙) ⟩
      (f 𝟙) ∧ ¬ (f 𝟙)
        ≡⟨ ¬Cancels∧R ⟩
      𝟘 ∎

    pres1 : f 𝟙 ≡ 𝟙
    pres1 =
      f 𝟙
        ≡⟨ cong f (sym ¬0≡1) ⟩
      f (¬ 𝟘)
        ≡⟨ pres¬ 𝟘 ⟩
      ¬ (f 𝟘)
        ≡⟨ cong ¬_ pres0 ⟩
      ¬ 𝟘
        ≡⟨ ¬0≡1 ⟩
      𝟙 ∎

    pres∨ : ∀ x y → f (x ∨ y) ≡ (f x) ∨ (f y)
    pres∨ x y =
      f (x ∨ y)
        ≡⟨ cong f (sym ¬Invol) ⟩
      f (¬ (¬ (x ∨ y)))
        ≡⟨ pres¬ _ ⟩
      ¬ (f (¬ (x ∨ y)))
        ≡⟨ cong ¬_ (cong f DeMorgan¬∨) ⟩
      ¬ (f (¬ x ∧ ¬ y))
        ≡⟨ cong ¬_ (pres∧ (¬ x) (¬ y)) ⟩
      ¬ (f (¬ x) ∧ f (¬ y))
        ≡⟨ cong ¬_ (cong₂ _∧_ (pres¬ x) (pres¬ y)) ⟩
      ¬ (¬ (f x) ∧ ¬ (f y))
        ≡⟨ DeMorgan¬∧ ⟩
      ¬ (¬ (f x)) ∨ ¬ (¬ (f y))
        ≡⟨ cong₂ _∨_ ¬Invol ¬Invol ⟩
      (f x) ∨ (f y) ∎

    pres+ : ∀ x y → f (x + y) ≡ (f x) + (f y)
    pres+ x y =
      f (x + y)
        ≡⟨ cong f (+FromBooleanAlgebraStr A) ⟩
      f ((x ∧ ¬ y) ∨ (¬ x ∧ y))
        ≡⟨ pres∨ _ _ ⟩
      f (x ∧ ¬ y) ∨ f (¬ x ∧ y)
        ≡⟨ cong₂ _∨_ (pres∧ x (¬ y)) (pres∧ (¬ x) y) ⟩
      (f x ∧ f (¬ y)) ∨ (f (¬ x) ∧ f y)
        ≡⟨ cong₂ _∨_ (cong (f x ∧_) (pres¬ y)) (cong (_∧ f y) (pres¬ x)) ⟩
      (f x ∧ ¬ (f y)) ∨ (¬ (f x) ∧ f y)
        ≡⟨ sym (+FromBooleanAlgebraStr B) ⟩
      (f x) + (f y) ∎

    pres- : ∀ x → f (- x) ≡ - (f x)
    pres- x =
      f (- x)
        ≡⟨ cong f (sym -IsId) ⟩
      f x
        ≡⟨ -IsId ⟩
      - (f x) ∎

    isBoolRingHom : IsCommRingHom (snd $ BooleanRing→CommRing A) f (snd (BooleanRing→CommRing B))
    IsCommRingHom.pres0 isBoolRingHom = pres0
    IsCommRingHom.pres1 isBoolRingHom = pres1
    IsCommRingHom.pres+ isBoolRingHom = pres+
    IsCommRingHom.pres· isBoolRingHom = pres·
    IsCommRingHom.pres- isBoolRingHom = pres-

    asBoolHom : BoolHom A B
    asBoolHom = f , isBoolRingHom

  module FromPres¬∨
    (pres¬ : ∀ x → f (¬ x) ≡ ¬ (f x))
    (pres∨ : ∀ x y → f (x ∨ y) ≡ (f x) ∨ (f y))
    where

    pres∧ : ∀ x y → f (x ∧ y) ≡ (f x) ∧ (f y)
    pres∧ x y =
      f (x ∧ y)
        ≡⟨ cong f (sym ¬Invol) ⟩
      f (¬ (¬ (x ∧ y)))
        ≡⟨ pres¬ _ ⟩
      ¬ (f (¬ (x ∧ y)))
        ≡⟨ cong ¬_ (cong f DeMorgan¬∧) ⟩
      ¬ (f (¬ x ∨ ¬ y))
        ≡⟨ cong ¬_ (pres∨ (¬ x) (¬ y)) ⟩
      ¬ (f (¬ x) ∨ f (¬ y))
        ≡⟨ cong ¬_ (cong₂ _∨_ (pres¬ x) (pres¬ y)) ⟩
      ¬ (¬ (f x) ∨ ¬ (f y))
        ≡⟨ DeMorgan¬∨ ⟩
      ¬ (¬ (f x)) ∧ ¬ (¬ (f y))
        ≡⟨ cong₂ _∧_ ¬Invol ¬Invol ⟩
      (f x) ∧ (f y) ∎

    open FromPres¬∧ pres¬ pres∧ public

