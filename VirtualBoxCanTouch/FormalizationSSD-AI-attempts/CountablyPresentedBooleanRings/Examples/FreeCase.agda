{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.Examples.FreeCase where 

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
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
import Cubical.Algebra.CommRing.Quotient.Base as Quot
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty as UP
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import WLPO
open import CommRingQuotients.EmptyQuotient
open import CountablyPresentedBooleanRings.PresentedBoole
open import Boole.EquivHelper 

module _ (α : binarySequence) where
  private 
    A = Σ[ n ∈ ℕ ] α n ≡ true
  module _ where
    open BooleanRingStr ⦃...⦄
    instance 
      _ = snd $ freeBA A 
      _ = snd $ freeBA ℕ 
  
    gensNotInAHelper : (n : ℕ) → Dec (α n ≡ true) → ⟨ freeBA ℕ ⟩
    gensNotInAHelper n (yes p) = 𝟘
    gensNotInAHelper n (no ¬p) = generator n 
    
    gensThatAreNotInA : (n : ℕ) → ⟨ freeBA ℕ ⟩
    gensThatAreNotInA n = gensNotInAHelper n (α n =B true) 

    gensNotInANoCaseHelper : (n : ℕ) → (¬αn : ¬ α n ≡ true) → 
                             (αn : Dec (α n ≡ true)) → 
                             gensNotInAHelper n αn ≡ generator n 
    gensNotInANoCaseHelper n ¬αn (yes p) = ex-falso $ ¬αn p
    gensNotInANoCaseHelper n ¬αn (no ¬p) = refl 

    gensNotInANoCase : (n : ℕ) → (¬αn : ¬ α n ≡ true) → gensThatAreNotInA n ≡ generator n
    gensNotInANoCase n ¬p = gensNotInANoCaseHelper n ¬p (α n =B true) 

    freeAcp : BooleanRing _
    freeAcp = freeBA ℕ /Im gensThatAreNotInA
    
    instance
      _ = snd freeAcp
   
    gensℕinFreeAHelper : (n : ℕ) → Dec (α n ≡ true) → ⟨ freeBA A ⟩
    gensℕinFreeAHelper n (yes p) = generator (n , p)
    gensℕinFreeAHelper n (no ¬p) = 𝟘 
    
    gensℕinFreeA : (n : ℕ) → ⟨ freeBA A ⟩
    gensℕinFreeA n = gensℕinFreeAHelper n (α n =B true) 

    gensℕinFreeAYesCaseHelper : (a : A) → (αn : Dec (α (fst a) ≡ true)) → 
                              gensℕinFreeAHelper (fst a) (αn) ≡ generator a
    gensℕinFreeAYesCaseHelper a (yes p) = cong generator (Σ≡Prop (λ _ → isSetBool _ _) refl)
    gensℕinFreeAYesCaseHelper a (no ¬p) = ex-falso (¬p (snd a)) 
    
    gensℕinFreeAYesCase : (a : A) → gensℕinFreeA (fst a) ≡ generator a
    gensℕinFreeAYesCase a = gensℕinFreeAYesCaseHelper a (α (fst a) =B true) 

    gensℕinFreeANoCaseHelper : (n : ℕ) → (¬αn : ¬ (α n ≡ true)) → (αn : Dec (α n ≡ true)) → 
                               gensℕinFreeAHelper n αn ≡ 𝟘 
    gensℕinFreeANoCaseHelper n ¬αn (yes p) = ex-falso $ ¬αn p 
    gensℕinFreeANoCaseHelper n ¬αn (no ¬p) = refl

    gensℕinFreeANoCase : (n : ℕ) → (¬αn : ¬ (α n ≡ true)) → gensℕinFreeA n ≡ 𝟘 
    gensℕinFreeANoCase n ¬p = gensℕinFreeANoCaseHelper n ¬p (α n =B true) 
   
    freeℕ→freeA : BoolHom (freeBA ℕ) (freeBA A)
    freeℕ→freeA = inducedBAHom ℕ (freeBA A) gensℕinFreeA
    
    open IsCommRingHom ⦃...⦄
    instance
      _ = (snd freeℕ→freeA) 

    AignoresOutsideAHelper : (n : ℕ) → (αn : Dec (α n ≡ true)) → freeℕ→freeA $cr gensNotInAHelper n αn ≡ 𝟘 
    AignoresOutsideAHelper n (yes p) = pres0
    AignoresOutsideAHelper n (no ¬p) = 
      freeℕ→freeA $cr generator n 
        ≡⟨ funExt⁻ (evalBAInduce ℕ (freeBA A) gensℕinFreeA) n ⟩ 
      gensℕinFreeA n  
        ≡⟨ useDecidabilityIsUnqiue n (no ¬p) ⟩ 
      gensℕinFreeAHelper n (no ¬p)  
        ≡⟨⟩ 
      𝟘 ∎ where
      useDecidabilityIsUnqiue : (n : ℕ) → (αn : Dec (α n ≡ true)) → 
                                gensℕinFreeA n ≡ gensℕinFreeAHelper n αn
      useDecidabilityIsUnqiue n αn = cong (gensℕinFreeAHelper n) $ 
        (α n =B true) ≡⟨ isPropDec (isSetBool (α n) true) (α n =B true) αn ⟩ αn ∎ 

    AignoresOutsideA : (n : ℕ) → freeℕ→freeA $cr gensThatAreNotInA n ≡ 𝟘 
    AignoresOutsideA n = AignoresOutsideAHelper n (α n =B true) 

    freeAcp→freeA : BoolHom freeAcp (freeBA A)
    freeAcp→freeA = QB.inducedHom (freeBA A) freeℕ→freeA AignoresOutsideA 
    
    freeA→freeℕ : BoolHom (freeBA A) (freeBA ℕ)
    freeA→freeℕ = inducedBAHom A (freeBA ℕ) (generator ∘ fst) 
  
    freeA→freeAcp : BoolHom (freeBA A) (freeAcp)
    freeA→freeAcp = quotientImageHom ∘cr freeA→freeℕ 

    freeA→freeA≡idOnGens : (a : A) → (freeAcp→freeA ∘cr freeA→freeAcp) $cr generator a ≡ generator a
    freeA→freeA≡idOnGens a = 
      (freeAcp→freeA ∘cr quotientImageHom ∘cr freeA→freeℕ) $cr generator a 
        ≡⟨ 
          cong (λ y → (freeAcp→freeA ∘cr quotientImageHom) $cr y) 
          (funExt⁻ (evalBAInduce A (freeBA ℕ) (generator ∘ fst)) a) 
         ⟩ 
      (freeAcp→freeA ∘cr quotientImageHom) $cr generator (fst a) 
        ≡⟨⟩
      ((QB.inducedHom _ freeℕ→freeA _) ∘cr quotientImageHom)  $cr generator (fst a) 
        ≡⟨ 
          cong (λ h → h $cr generator (fst a)) 
          (QB.evalInduce _) 
         ⟩
      freeℕ→freeA $cr generator (fst a) 
        ≡⟨ 
          cong (λ h → h (fst a)) 
          (evalBAInduce ℕ (freeBA A) gensℕinFreeA)
         ⟩
      gensℕinFreeA (fst a) 
        ≡⟨ gensℕinFreeAYesCase a ⟩
      generator a ∎

    freeA→freeA≡id : (freeAcp→freeA ∘cr freeA→freeAcp) ≡ idCommRingHom (BooleanRing→CommRing (freeBA A))
    freeA→freeA≡id = equalityFromEqualityOnGenerators (freeBA A) _ _ freeA→freeA≡idOnGens

    instance 
      _ = snd (quotientImageHom {B = freeBA ℕ } {f = gensThatAreNotInA} ∘cr freeA→freeℕ) 

    quotientOutNotAAgreesWithAOnGensHelper : (n : ℕ) → (Dec (α n ≡ true)) → 
      quotientImageHom {B = freeBA ℕ} {f = gensThatAreNotInA} $cr 
      (freeA→freeℕ $cr gensℕinFreeA n)
      ≡ 
      quotientImageHom {B = freeBA ℕ} {f = gensThatAreNotInA} $cr 
      generator n

    quotientOutNotAAgreesWithAOnGensHelper n (yes p) = 
      quotientImageHom $cr ( (freeA→freeℕ) $cr  (gensℕinFreeA n)) 
        ≡⟨ 
          cong (λ x → quotientImageHom $cr (freeA→freeℕ $cr x)) 
          (gensℕinFreeAYesCase (n , p))
         ⟩ 
      quotientImageHom $cr (((fst (freeA→freeℕ)) ∘ generator) (n , p)) 
        ≡⟨ cong (λ h → quotientImageHom $cr (h (n , p) )) (evalBAInduce _ _ _) ⟩
      quotientImageHom $cr (generator ∘ fst {B = (λ n → α n ≡ true)}) (n , p) 
        ≡⟨⟩
      quotientImageHom $cr generator n  ∎ 
    quotientOutNotAAgreesWithAOnGensHelper n (no ¬p) =  lhs=0 ∙ (sym rhs=0)  where
      
      genn=0Helper : (αn : Dec (α n ≡ true)) →  gensℕinFreeAHelper n αn ≡ 𝟘 
      genn=0Helper (yes p) = ex-falso $ ¬p p
      genn=0Helper (no ¬p) = refl 

      genn=0 : gensℕinFreeA n ≡ 𝟘 
      genn=0 = genn=0Helper (α n =B true)

      lhs=0 : quotientImageHom {B = freeBA ℕ } {f = gensThatAreNotInA } $cr 
               ((freeA→freeℕ) $cr  (gensℕinFreeA n)) ≡ 𝟘 
      lhs=0 = cong (λ x → quotientImageHom $cr (freeA→freeℕ $cr x)) genn=0 ∙ pres0
    
      rhs=0 : quotientImageHom {B = freeBA ℕ} {f = gensThatAreNotInA } $cr generator n ≡ 𝟘 
      rhs=0 = cong (fst quotientImageHom) (sym $ gensNotInANoCase n ¬p) ∙ zeroOnImage n 

    quotientOutNotAAgreesWithAOnGens : (n : ℕ) → 
      quotientImageHom $cr ( (freeA→freeℕ) $cr (gensℕinFreeA n)) 
      ≡ 
      quotientImageHom $cr generator n
    quotientOutNotAAgreesWithAOnGens n = quotientOutNotAAgreesWithAOnGensHelper n (α n =B true) 

    freeAcp→freeAcp∘q≡qOnGens : (n : ℕ) → 
      (freeA→freeAcp ∘cr freeAcp→freeA) $cr (quotientImageHom $cr generator n) 
      ≡ 
      quotientImageHom $cr (generator n)

    freeAcp→freeAcp∘q≡qOnGens n = 
      (freeA→freeAcp ∘cr freeAcp→freeA ∘cr quotientImageHom) $cr generator n 
         ≡⟨⟩ 
      (freeA→freeAcp ∘cr ((QB.inducedHom (freeBA A) freeℕ→freeA _) ∘cr quotientImageHom)) $cr generator n
         ≡⟨ cong (λ h → (freeA→freeAcp ∘cr h) $cr generator n) (QB.evalInduce _ ) ⟩ 
      (freeA→freeAcp ∘cr freeℕ→freeA) $cr generator n
         ≡⟨ cong (λ x → freeA→freeAcp $cr x ) (funExt⁻ (evalBAInduce _ _ _) n ) ⟩ 
      freeA→freeAcp $cr gensℕinFreeA n
         ≡⟨⟩
      quotientImageHom $cr (freeA→freeℕ $cr gensℕinFreeA n)
         ≡⟨ quotientOutNotAAgreesWithAOnGens n ⟩ 
       quotientImageHom $cr generator n
         ∎  

    freeAcp→freeAcp∘q≡q : (freeA→freeAcp ∘cr freeAcp→freeA ∘cr quotientImageHom) ≡ quotientImageHom 
    freeAcp→freeAcp∘q≡q = equalityFromEqualityOnGenerators freeAcp _ _ freeAcp→freeAcp∘q≡qOnGens 
    
    freeAcp→freeAcp≡id : fst (freeA→freeAcp ∘cr freeAcp→freeA) ≡ idfun ⟨ freeAcp ⟩ 
    freeAcp→freeAcp≡id = quotientImageHomEpi (_ ,  λ _ _ → is-set _ _ ) (cong fst freeAcp→freeAcp∘q≡q) 

    freeAcp≃freeA : BooleanRingEquiv freeAcp (freeBA A)
    freeAcp≃freeA = isoToCommRingEquiv freeAcp→freeA (fst freeA→freeAcp) 
      (λ x → cong (λ h → h $cr x)  freeA→freeA≡id)
      (funExt⁻ freeAcp→freeAcp≡id )

replacementFreeOnCountableHelper : (α : binarySequence) → has-Boole-ω' (freeBA (Σ[ n ∈ ℕ ] α n ≡ true))
replacementFreeOnCountableHelper α = gensThatAreNotInA α , (invCommRingEquiv _ _ $ freeAcp≃freeA α) 

replacementFreeOnCountable : (A : Type) → has-Countability-structure A → has-Boole-ω' (freeBA A)
replacementFreeOnCountable A (α , A=Σα) = subst (has-Boole-ω' ∘ freeBA) (sym $ isoToPath A=Σα) (replacementFreeOnCountableHelper α)
