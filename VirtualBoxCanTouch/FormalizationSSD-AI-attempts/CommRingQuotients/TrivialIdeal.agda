{-# OPTIONS --cubical --guardedness #-}

module CommRingQuotients.TrivialIdeal where 
{- This file shows for a Ring R and Ideal I, that if R/I is trivial, then 1 ∈ I -}


open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order 
open <-Reasoning

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base

open import Cubical.Tactics.CommRingSolver

module _ {ℓ : Level} (R : CommRing ℓ) (I : IdealsIn R) where
  open CommRingStr ⦃...⦄
  instance 
    _ = (snd (R / I))
    _ = snd R
  private 
    π = quotientHom R I 

  opaque 
    unfolding kernel≡I 
  
    quotientFiber : (x y : ⟨ R ⟩ ) → fst π x ≡ fst π y → (x - y) ∈ fst I 
    quotientFiber x y p = transport (cong (λ J → (x - y) ∈ (fst J) ) kernelπ=I)  $ equalIfDiffInKernelπ x y p  where
      kernelπ=I : CK.kernelIdeal R (R / I) π ≡ I 
      kernelπ=I = kernel≡I I
  
      equalIfDiffInKernelπ :  (x y : ⟨ R ⟩ ) → π $cr x ≡ π $cr y → x - y ∈ fst (CK.kernelIdeal R (R / I ) π )
      equalIfDiffInKernelπ x y p = CK.kernelFiber R (R / I)  π  x y p 

  open IsCommRingHom (snd π)
  
  trivialQuotient→1∈I : _≡_ {A = ⟨ R / I ⟩} 1r 0r → 1r ∈ fst I 
  trivialQuotient→1∈I p = 
    transport (cong (λ a → a ∈ fst I ) q) (quotientFiber 1r 0r p')  where
      p' : π $cr 1r ≡ π  $cr 0r
      p' = pres1 ∙ p ∙ sym pres0 
      q : 1r - 0r ≡ 1r 
      q = solve! R 
