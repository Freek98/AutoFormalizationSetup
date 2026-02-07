{-# OPTIONS --cubical --guardedness #-}

module CommRingQuotients.EmptyQuotient where

{- We show that quotienting over the empty function does not change the ring -}

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.Structure
open import Cubical.Functions.Surjection

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing.Quotient.ImageQuotient
open import Cubical.HITs.SetQuotients 
open import Cubical.Algebra.CommRing.Quotient.Base
open import Cubical.Algebra.CommRing.Ideal.Base 
open import CommRingQuotients.IdealTerms
open import CommRingQuotients.TrivialIdeal


open import Cubical.Data.Empty renaming (rec* to empty-func)
open import Cubical.Tactics.CommRingSolver
import Cubical.Algebra.CommRing.Kernel as CK 

module _ {ℓ : Level} (R : CommRing ℓ) where 
  private
    R' : CommRing ℓ 
    R' = R /Im empty-func 
  open CommRingStr ⦃...⦄
  instance 
   _ = snd R
   _ = snd R'

  kernelEmpty : IdealsIn R
  kernelEmpty = genIdeal R empty-func
  
  trivKern : (i : ⟨ R ⟩) → isInIdeal R empty-func i → i ≡ 0r
  trivKern i (iszero .i 0=i) = sym 0=i  
  trivKern i (isSum  .i s t i=s+t s∈I t∈I) = 
    i       ≡⟨ i=s+t ⟩ 
    s  + t  ≡⟨ cong₂ _+_ (trivKern s s∈I) (trivKern t t∈I) ⟩ 
    0r + 0r ≡⟨ +IdL 0r ⟩ 
    0r      ∎ 
  trivKern i (isMul  .i s t i=st t∈I) = 
    i      ≡⟨ i=st ⟩ 
    s · t  ≡⟨ cong (_·_ s) (trivKern t t∈I) ⟩
    s · 0r ≡⟨ solve! R ⟩ 
    0r     ∎  
  private
    π  = quotientImageHom R empty-func
    I' : IdealsIn R
    I' = (genIdeal R empty-func)

  fiberProp : (c : ⟨ R' ⟩) → isProp (fiber (fst π) c)
  fiberProp c (x , qx=c) (y , qy=c) = Σ≡Prop (λ d → is-set _ _) help'' where
    help : x - y ∈ fst I'
    help = quotientFiber R I' x y (qx=c ∙ sym qy=c) 

    help' : x - y ≡ 0r
    help' = PT.rec (is-set _ _) (trivKern (x - y)) (idealDecomp R empty-func (x - y) help)

    help'' : x ≡ y -- I know this exists as a function, TODO look up the name
    help'' = x ≡⟨ solve! R ⟩ x - y + y ≡⟨ cong (λ a → a + y) help' ⟩ 0r + y ≡⟨ solve! R ⟩ y ∎  
 
  fiberInhabited : (c : ⟨ R' ⟩) → fiber (fst π) c
  fiberInhabited c = transport (propTruncIdempotent (fiberProp c)) (quotientHomSurjective R I' c)

  emptyQuotientEquiv : CommRingEquiv R R'
  fst (fst emptyQuotientEquiv) = fst $ π
  equiv-proof (snd (fst emptyQuotientEquiv)) y = fiberInhabited y , fiberProp y _ 
  snd emptyQuotientEquiv = snd $ π
