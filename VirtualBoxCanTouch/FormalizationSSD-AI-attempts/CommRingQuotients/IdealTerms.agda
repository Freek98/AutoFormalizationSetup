{-# OPTIONS --cubical -WnoUselessAbstract  -WnoUnsupportedIndexedMatch -WnoInteractionMetaBoundaries --guardedness #-}

module CommRingQuotients.IdealTerms where 

open import Cubical.Functions.Fixpoint

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.FreeBool

open  import BooleanRing.FreeBooleanRing.SurjectiveTerms
open  import BooleanRing.FreeBooleanRing.freeBATerms

open import QuotientBool
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base
open import Cubical.Tactics.CommRingSolver

open import BasicDefinitions 

module _ {ℓ : Level} (R : CommRing ℓ) {X : Type ℓ} (f : X → ⟨ R ⟩)  where
  open CommRingStr ⦃...⦄
  instance 
   _ = (snd R) 
  data isInIdeal : (r : ⟨ R ⟩) → Type ℓ where
        isImage  : (r : ⟨ R ⟩) → (x : X) → (f x ≡ r) → isInIdeal r
        iszero   : (r : ⟨ R ⟩) → (0r ≡ r) → isInIdeal r
        isSum    : (r : ⟨ R ⟩) → (s t : ⟨ R ⟩) → (r ≡ s + t) → isInIdeal s → isInIdeal t → isInIdeal r
        isMul    : (r : ⟨ R ⟩) → (s t : ⟨ R ⟩) → (r ≡ s · t) →               isInIdeal t → isInIdeal r

  idealDecomp : ( r : ⟨ R ⟩ ) → IQ.generatedIdeal R f r → ∥ isInIdeal r ∥₁
  idealDecomp .(f x)   (IQ.single x)                    = ∣ isImage (f x) x refl ∣₁
  idealDecomp .(0r)     IQ.zero                         = ∣ iszero 0r refl ∣₁
  idealDecomp .(s + t) (IQ.add {x = s} {y = t} s∈I t∈I) = PT.map2 (isSum (s + t) s t refl) (idealDecomp s s∈I) (idealDecomp t t∈I)
  idealDecomp .(s · t) (IQ.mul {r = s} {x = t} t∈I )    = PT.map  (isMul (s · t) s t refl) (idealDecomp t t∈I)
  idealDecomp r        (IQ.squash r∈I r∈I' i)           = ∥∥-isPropDep isInIdeal 
                                                          (idealDecomp r r∈I) (idealDecomp r r∈I') refl i 
