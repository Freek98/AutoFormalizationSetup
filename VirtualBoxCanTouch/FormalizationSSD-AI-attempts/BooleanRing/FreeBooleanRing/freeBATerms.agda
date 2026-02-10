{-# OPTIONS --cubical --guardedness #-}

module BooleanRing.FreeBooleanRing.freeBATerms where
{- This file shows that the terms of a freely generated Boolean ring have a surjection into that freely generated Boolean ring. -}


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Surjection

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Quotient.ImageQuotient
open import Cubical.Algebra.CommRing.Quotient.Base

open import Cubical.Algebra.BooleanRing
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.SurjectiveTerms
open  import BooleanRing.FreeBooleanRing.FreeBool

freeBATerms : {ℓ : Level} → Type ℓ → Type ℓ
freeBATerms A = TermsOf BoolCR [ A ]

opaque 
  unfolding freeBA 
  includeBATermsSurj : {A : Type} → freeBATerms A ↠ ⟨ freeBA A ⟩ 
  includeBATermsSurj {A} = compSurjection 
    (includeTerm , hasTerm) 
    (fst (quotientImageHom _ _) , quotientHomSurjective _ (idemIdeal _)) 

module _ {ℓ : Level} {A : Type} (B : BooleanRing ℓ) (f g : BoolHom (freeBA A) B) 
         (agreeOnGens : ((a : A) → (f $cr generator a ≡ g $cr generator a))) where 
  open IsCommRingHom
  open BooleanRingStr ⦃...⦄
  instance
    _ = snd $ freeBA A
    _ = snd B 
  opaque
    unfolding generator
    unfolding includeBATermsSurj
    equalityFromEqualityOnGenerators : f ≡ g
    equalityFromEqualityOnGenerators = CommRingHom≡ $
                                       funExt λ x → PT.rec (is-set (f $cr x) (g $cr x)) 
                                       (λ (t , πt=x) → cong (fst f) (sym πt=x) ∙ agreeOnTerms t ∙ cong (fst g) πt=x) $
                                       snd includeBATermsSurj x where
      π : freeBATerms A → ⟨ freeBA A ⟩
      π = fst includeBATermsSurj

      agreeOnTerms : (t : freeBATerms A) → f $cr fst includeBATermsSurj t ≡ g $cr fst includeBATermsSurj t
      agreeOnTerms (Tvar g)       = agreeOnGens g
      agreeOnTerms (Tconst false) = pres0 (snd f) ∙ (sym $ pres0 (snd g))
      agreeOnTerms (Tconst true)  = pres1 (snd f) ∙ (sym $ pres1 (snd g))
      agreeOnTerms (t +T s)       = f $cr (π t + π s) 
                                      ≡⟨ pres+ (snd f) (π t) (π s) ⟩ 
                                    (f $cr π t ) + (f $cr π s) 
                                      ≡⟨ cong₂ _+_ (agreeOnTerms t) (agreeOnTerms s) ⟩ 
                                    (g $cr π t) + (g $cr π s) 
                                      ≡⟨ sym $ pres+ (snd g) (π t) (π s) ⟩ 
                                    g $cr (π t + π s)∎ 
      agreeOnTerms (-T t)         = pres- (snd f) (π t) ∙ 
                                    cong -_ (agreeOnTerms t) ∙ 
                                    (sym $ pres- (snd g) (π t))
      agreeOnTerms (t ·T s)       = pres· (snd f) (π t) (π s) ∙ 
                                    cong₂ _·_ (agreeOnTerms t) (agreeOnTerms s) ∙ 
                                    (sym $ pres· (snd g) (π t) (π s)) 
  



