{-# OPTIONS --cubical --guardedness #-}
module formalization.Library.StoneSpaces.Examples.ClosedProp where

open import formalization.Library.StoneSpaces.Spectrum
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import formalization.Library.PropositionalTopology.OpenClosedProps

open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.BooleanRing
open import Cubical.HITs.PropositionalTruncation as PT

open import formalization.Library.CountablyPresentedBooleanRings.Examples.Bool
open import formalization.Library.CountablyPresentedBooleanRings.Examples.TrivialBA
open import formalization.Library.BooleanRing.BooleanRingQuotients.QuotientBool
open import formalization.Library.CountablyPresentedBooleanRings.Definitions
open import formalization.Library.CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import formalization.Library.CountablyPresentedBooleanRings.Examples.BoolQuotientByBinarySequence
open import formalization.Library.BooleanRing.FreeBooleanRing.FreeBool
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing.Initial

open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import formalization.Library.AntiEquivalence
open import formalization.Library.BasicDefinitions

-- Goal : lemma 1.1.9 of the paper. 
module ClosedPropIsStone (α : binarySequence) where
  All0 : Type₀ 
  All0 = ∀ (n : ℕ) → α n ≡ false 

  B : countablyPresentedBooleanRing
  B = 2/α α

  open BooleanRingStr (snd (fst B))

  ∀0→SpB : All0 → Sp B
  ∀0→SpB α=0 = inducedHom BoolBR (BoolBR→ BoolBR) λ n → 
    BoolBR→ BoolBR $cr α n 
     ≡⟨ cong (fst (BoolBR→ BoolBR)) (α=0 n) ⟩ 
    BoolBR→ BoolBR $cr false
     ≡⟨⟩ 
    false ∎
  
  open IsCommRingHom 
  SpB→∀0 : Sp B → All0 
  SpB→∀0 f n = ¬true→false (α n) λ αn=1 → false≢true $
    false 
      ≡⟨ (sym $ pres0 (snd f)) ⟩ 
    f $cr 𝟘
      ≡⟨ cong (fst f) (sym (zeroOnImage n)) ⟩ 
    (f ∘cr quotientImageHom) $cr α n
      ≡⟨ cong (fst $ f ∘cr quotientImageHom) αn=1 ⟩ 
    (f ∘cr quotientImageHom) $cr true
      ≡⟨ pres1 (snd (f ∘cr quotientImageHom)) ⟩ 
    true ∎   
 
  isPropSpB : isProp (Sp B)
  isPropSpB f g = CommRingHom≡ (funExt λ b → PT.rec (isSetBool (f $cr b) (g $cr b)) 
    (agreeOn01 b) (quotientByBinary.max2inQuotient α b)) where
    agreeOn01 : (b : ⟨ fst B ⟩) → (b ≡ 𝟘) ⊎ (b ≡ 𝟙) → f $cr b ≡ g $cr b
    agreeOn01 b (inl b=0) = 
      f $cr b ≡⟨ cong (fst f) b=0 ⟩ 
      f $cr 𝟘 ≡⟨ pres0 (snd f) ⟩ 
      false   ≡⟨ (sym $ pres0 (snd g)) ⟩ 
      g $cr 𝟘 ≡⟨ (sym $ cong (fst g) b=0) ⟩ 
      g $cr b ∎
    agreeOn01 b (inr b=1) =
      f $cr b ≡⟨ cong (fst f) b=1 ⟩ 
      f $cr 𝟙 ≡⟨ pres1 (snd f) ⟩ 
      true    ≡⟨ sym $ pres1 (snd g) ⟩ 
      g $cr 𝟙 ≡⟨ sym $ cong (fst g) b=1 ⟩ 
      g $cr b ∎
  
  SpB=All0 : Sp B ≡ All0
  SpB=All0 = hPropExt isPropSpB (isPropΠ λ _ → isSetBool _ _) SpB→∀0 ∀0→SpB 

  isStoneAll0 : hasStoneStr All0
  isStoneAll0 .fst = B
  isStoneAll0 .snd = SpB=All0 

  total : StoneSpace
  total .fst = All0
  total .snd = isStoneAll0 

isStoneClosedPropWitness : (P : hProp ℓ-zero) → isClosedWitness P → hasStoneStr ⟨ P ⟩
isStoneClosedPropWitness P (α , P↔∀α) = subst hasStoneStr (hPropExt (isPropΠ (λ _ → isSetBool _ _)) (snd P) (snd P↔∀α) (fst P↔∀α)) (ClosedPropIsStone.isStoneAll0 α)

  
