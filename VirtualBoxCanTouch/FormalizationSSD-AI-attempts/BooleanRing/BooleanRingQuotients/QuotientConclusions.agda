{-# OPTIONS --cubical --guardedness #-}

module BooleanRing.BooleanRingQuotients.QuotientConclusions  where 
{- We show that the quotient of a Boolean Ring agrees with that of the underlying commutative Ring -}


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
open import Cubical.Algebra.CommRing.Univalence
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
open import WLPO
open import CommRingQuotients.EmptyQuotient
open import CountablyPresentedBooleanRings.PresentedBoole
open import Cubical.Algebra.CommRing.Univalence 

open import CountablyPresentedBooleanRings.Examples.FreeCase 
open import Boole.EquivHelper
open import BooleanRing.BooleanRingQuotients.QuotientCase 

opaque
  unfolding QB._/Im_
  quotientCheck : (A : BooleanRing ℓ-zero) → {X : Type} → (f : X → ⟨ A ⟩ ) → 
    (BooleanRing→CommRing A) IQ./Im f ≡ BooleanRing→CommRing (A QB./Im f)
  quotientCheck A f = refl 

  sameUnderlyingSet : (A : BooleanRing ℓ-zero) → (fst A) ≡ fst (BooleanRing→CommRing A)
  sameUnderlyingSet A = refl



--opaque 
--  unfolding QB.quotientImageHom
--  unfolding QB._/Im_
--  quotientImageCheck : (A : BooleanRing ℓ-zero) → {X : Type} → (f : X → ⟨ A ⟩) → 
--    (fst (IQ.quotientImageHom (BooleanRing→CommRing A) f)) ≡ (fst (QB.quotientImageHom {B = A} {f = f}))
--  quotientImageCheck A f = {! !} 

opaque
  unfolding QB.quotientImageHom
  unfolding QB._/Im_
  BoolQuotientEquiv : (A : BooleanRing ℓ-zero) (f g : ℕ → ⟨ A ⟩) → 
    BooleanRing→CommRing (A QB./Im (⊎.rec f g)) ≡
    BooleanRing→CommRing ((A QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
  BoolQuotientEquiv A f g =  
    BooleanRing→CommRing (A QB./Im (⊎.rec f g)) 
      ≡⟨⟩ 
    (BooleanRing→CommRing A) IQ./Im (⊎.rec f g)
      ≡⟨ (uaCommRing $ quotientConclusion (BooleanRing→CommRing A) f g) ⟩ 
    ((BooleanRing→CommRing A) IQ./Im f) IQ./Im ((fst $ IQ.quotientImageHom (BooleanRing→CommRing A) f)∘ g)
      ≡⟨⟩ 
--    ((BooleanRing→CommRing A) IQ./Im f) IQ./Im ((fst $ QB.quotientImageHom {B = A} {f = f})∘ g)
--      ≡⟨⟩ -- ⟨ cong (λ B → B IQ./Im  ((fst $ QB.quotientImageHom {B = A} {f = f}) ∘ g)) (quotientCheck A f) ⟩
--    (BooleanRing→CommRing (A QB./Im f)) IQ./Im ((fst $ QB.quotientImageHom {B = A} {f = f})∘ g)
--      ≡⟨⟩ 
    BooleanRing→CommRing ((A QB./Im f) QB./Im ( (fst $ QB.quotientImageHom {B = A} {f = f}) ∘ g)) ∎ 


--  BoolQuotientEquiv : (A : BooleanRing ℓ-zero) (f g : ℕ → ⟨ A ⟩) → --BooleanRingEquiv
--    (A QB./Im (⊎.rec f g)) ≡
--    ((A QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
--  BoolQuotientEquiv A f g = -- quotientConclusion (BooleanRing→CommRing A) f g
--    A QB./Im (⊎.rec f g) ≡⟨ {! !} ⟩ 
--    (BooleanRing→CommRing A) QB./Im (⊎.rec f g) ≡⟨ {! !} ⟩ 
--    ((A QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g)) ∎
----    (BooleanRing→CommRing A
