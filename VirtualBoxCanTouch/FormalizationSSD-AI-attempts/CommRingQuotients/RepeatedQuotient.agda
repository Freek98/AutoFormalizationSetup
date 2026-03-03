{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module CommRingQuotients.RepeatedQuotient where 
{- This module shows that if we have two maps f,g : X → A, then quotienting first by f, then by g and quotienting by f + g give the same result -} 

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import BooleanRing.BooleanRingMaps
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso ; rec* to empty-func)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning
open import Cubical.Data.Nat.Bijections.Sum

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.FreeBool
import BooleanRing.FreeBooleanRing.FreeBool as FB

open  import BooleanRing.FreeBooleanRing.SurjectiveTerms
open  import BooleanRing.FreeBooleanRing.freeBATerms

open import QuotientBool as QB
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base
open import Cubical.Algebra.CommRing.Quotient.ImageQuotient
import Cubical.Algebra.CommRing.Quotient.Base as Quot
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty as UP
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import BasicDefinitions
open import CommRingQuotients.EmptyQuotient
open import CountablyPresentedBooleanRings.Definitions
open import Cubical.Algebra.CommRing.Univalence 

open import CommRingQuotients.EquivHelper

module equ {ℓ : Level} (A : CommRing ℓ) {X : Type ℓ} (f : X → ⟨ A ⟩) where
  mapsOutOfX : (C : CommRing ℓ) → Type ℓ 
  mapsOutOfX C = X → ⟨ C ⟩ 
  
  transportMap : (B : CommRing ℓ) → (p : A ≡ B) → mapsOutOfX B
  transportMap B = J (λ B p → mapsOutOfX B) f

  transportMap' : (B : CommRing ℓ) → (p : A ≡ B) → mapsOutOfX B
  transportMap' B p = (fst $ fst $ (invEq $ CommRingPath A B) p) ∘ f 

  q : CommRingEquiv A A 
  q = (invEq $ (CommRingPath A A)) refl 

  q=id : fst (fst q) ≡ idfun ⟨ A ⟩ 
  q=id = funExt transportRefl 

  need : (B : CommRing ℓ) → (p : A ≡ B ) → transportMap B p ≡ transportMap' B p 
  need B = J (λ B p → transportMap B p ≡ transportMap' B p) $
    transportMap A refl ≡⟨ transportRefl f ⟩ 
    f ≡⟨⟩ 
    idfun ⟨ A ⟩  ∘ f ≡⟨ cong (λ g → g ∘ f) (sym q=id) ⟩ 
    fst (fst q)  ∘ f ≡⟨⟩ 
    transportMap' A refl ∎ 

  quot : (B : CommRing ℓ) → (p : A ≡ B) → (CommRing ℓ) 
  quot B p = B IQ./Im (transportMap B p)

  equalquot : (B : CommRing ℓ) → (p : A ≡ B) → quot B p ≡ A IQ./Im f
  equalquot B = J (λ B p → quot B p ≡ A IQ./Im f) $ cong (λ g → A IQ./Im g) (transportRefl f)

module sum {ℓ : Level} (A : CommRing ℓ) {X : Type ℓ} (f g : X → ⟨ A ⟩) where
  -- goal show that ((A / f) / π∘g ) ≡ ((A / g ) / π∘f) ≡ A/f+g
  f+g : X ⊎ X → ⟨ A ⟩
  f+g = ⊎.rec f g 
  
  A/f : CommRing ℓ
  A/f = A IQ./Im f 
  opaque
    ginA/f : X → ⟨ A/f ⟩
    ginA/f = (fst $ IQ.quotientImageHom A f) ∘ g

  opaque
    A/f/πg : CommRing ℓ
    A/f/πg = A/f IQ./Im ginA/f
    πg : CommRingHom A/f A/f/πg
    πg = IQ.quotientImageHom A/f ginA/f
  opaque
    πComp : CommRingHom A A/f/πg
    πComp = πg ∘cr IQ.quotientImageHom A f
  open CommRingStr ⦃...⦄
  instance 
    _ = (snd A/f/πg)
  open IsCommRingHom ⦃...⦄
  instance 
    _ = (snd πComp)
  opaque
    unfolding πComp
    unfolding ginA/f
    unfolding πg
    πComp0Ong : (x : X) → πComp $cr (g x) ≡ 0r 
    πComp0Ong x = IQ.zeroOnImage _ _ x
    
    πComp0Onf : (x : X) → πComp $cr (f x) ≡ 0r 
    πComp0Onf x = (cong (fst (IQ.quotientImageHom A/f ginA/f)) 
                  (IQ.zeroOnImage A f x)) ∙ pres0 
  opaque 
    A/f+g : CommRing ℓ
    A/f+g = A IQ./Im f+g
  opaque
    unfolding A/f+g
    sumToComp : CommRingHom A/f+g A/f/πg
    sumToComp = IQ.inducedHom A f+g πComp λ { (inl x) → πComp0Onf x
                                            ; (inr x) → πComp0Ong x } 
  opaque
    unfolding A/f+g
    πSum : CommRingHom A A/f+g
    πSum = IQ.quotientImageHom A f+g 
  instance 
    _ = snd πSum
    _ = snd A/f+g
  opaque
    unfolding πSum
    πSum0Onf : (x : X) → πSum $cr f x ≡ 0r
    πSum0Onf x = IQ.zeroOnImage A f+g (inl x) 
    
    πSum0Ong : (x : X) → πSum $cr g x ≡ 0r
    πSum0Ong x = IQ.zeroOnImage A f+g (inr x) 
  
  opaque
    unfolding πSum
    unfolding IQ.inducedHom
    unfolding ginA/f
    compToSumHelper : (x : X) → (IQ.inducedHom A f πSum πSum0Onf) $cr (ginA/f x) ≡ 0r
    compToSumHelper x = πSum0Ong x ∙ pres0

  opaque
    unfolding A/f/πg
    compToSum : CommRingHom A/f/πg A/f+g 
    compToSum = IQ.inducedHom A/f ginA/f (IQ.inducedHom A f πSum πSum0Onf) 
      compToSumHelper
  opaque
    unfolding compToSum
    unfolding πComp
    unfolding sumToComp
    unfolding πSum
    ret∘πSum : (compToSum ∘cr sumToComp) ∘cr πSum ≡ πSum
    ret∘πSum = 
      (compToSum ∘cr sumToComp) ∘cr πSum 
       ≡⟨ CommRingHom≡ refl ⟩ 
      compToSum ∘cr sumToComp ∘cr πSum 
       ≡⟨ cong (λ h → compToSum ∘cr h) $ IQ.evalInduce A ⟩ 
      compToSum ∘cr πComp
       ≡⟨ CommRingHom≡ refl ⟩ 
      (compToSum ∘cr IQ.quotientImageHom A/f _) ∘cr IQ.quotientImageHom A f 
       ≡⟨ cong (λ h → h ∘cr IQ.quotientImageHom A f) $ IQ.evalInduce A/f ⟩ 
      IQ.inducedHom A f πSum πSum0Onf ∘cr IQ.quotientImageHom A f
       ≡⟨ IQ.evalInduce A ⟩ 
      πSum 
       ∎     

  opaque 
    unfolding sumToComp
    unfolding πSum
    unfolding πComp
    unfolding compToSum
    sec∘πComp : (sumToComp ∘cr compToSum) ∘cr πComp ≡ πComp 
    sec∘πComp = (sumToComp ∘cr compToSum) ∘cr πComp 
                        ≡⟨ CommRingHom≡ refl ⟩
                     sumToComp ∘cr 
                     (IQ.inducedHom A/f ginA/f (IQ.inducedHom A f πSum πSum0Onf) compToSumHelper ∘cr ( (IQ.quotientImageHom A/f _)) )
                     ∘cr IQ.quotientImageHom A f
                        ≡⟨ cong (λ h → sumToComp ∘cr h ∘cr IQ.quotientImageHom A f) 
                           $ IQ.evalInduce A/f ⟩ 
                     sumToComp ∘cr (IQ.inducedHom A f πSum πSum0Onf) ∘cr IQ.quotientImageHom A f
                        ≡⟨ CommRingHom≡ refl ⟩ 
                     sumToComp ∘cr (IQ.inducedHom A f πSum πSum0Onf ∘cr IQ.quotientImageHom A f)
                        ≡⟨ cong (λ h → sumToComp ∘cr h) $ IQ.evalInduce A ⟩ 
                     sumToComp ∘cr πSum
                        ≡⟨ IQ.evalInduce A ⟩ 
                     πComp
                        ∎

  opaque 
    ret' : (compToSum ∘cr sumToComp) ∘cr πSum ≡ idCommRingHom A/f+g ∘cr πSum
    ret' = ret∘πSum ∙ (sym $ idCompCommRingHom πSum)
  
  opaque
    unfolding πSum
    ret : (compToSum ∘cr sumToComp) ≡ idCommRingHom A/f+g
    ret = IQ.quotientImageHomEpi A ret' 
  
  opaque
    unfolding A/f/πg
    unfolding A/f+g
    unfolding πComp
    sec' : (sumToComp ∘cr compToSum) ∘cr πComp ≡ idCommRingHom A/f/πg ∘cr πComp
    sec' = sec∘πComp ∙ (sym $ idCompCommRingHom πComp)
  opaque
    unfolding πComp
    sec'' : (((sumToComp ∘cr compToSum) ∘cr πg) ∘cr (IQ.quotientImageHom A f)) ≡ 
                 (idCommRingHom A/f/πg ∘cr πg) ∘cr IQ.quotientImageHom A f
    sec'' = (CommRingHom≡ refl) ∙ sec' ∙ (CommRingHom≡ refl)
  opaque 
    sec''' : (sumToComp ∘cr compToSum) ∘cr πg ≡ idCommRingHom A/f/πg ∘cr πg
    sec''' = IQ.quotientImageHomEpi A sec'' 
  opaque
    unfolding πg
    sec : sumToComp ∘cr compToSum ≡ idCommRingHom A/f/πg
    sec = IQ.quotientImageHomEpi A/f sec''' 
  opaque 
    conclusion : CommRingEquiv A/f+g A/f/πg
    conclusion = isoHomToCommRingEquiv sumToComp compToSum sec ret 

opaque
  unfolding sum.conclusion
  unfolding sum.A/f/πg
  unfolding sum.A/f+g
  unfolding sum.ginA/f
  quotientConclusion : {ℓ : Level} (A : CommRing ℓ) {X : Type ℓ} (f g : X → ⟨ A ⟩) → CommRingEquiv 
    (A IQ./Im (⊎.rec f g)) 
    ((A IQ./Im f) IQ./Im ((fst (IQ.quotientImageHom A f)) ∘ g))
  quotientConclusion A f g = sum.conclusion A f g 

