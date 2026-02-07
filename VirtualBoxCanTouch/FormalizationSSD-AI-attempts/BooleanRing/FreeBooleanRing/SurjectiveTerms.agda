{-# OPTIONS --cubical --guardedness #-}

module BooleanRing.FreeBooleanRing.SurjectiveTerms where 
{- 
-- In general, it should be true that for a higher inductive type X, 
-- the type of it's terms X_0 should have a surjection to X. 
-- In this file, we show that for the higher inductive type R[I}, as defined in the first import. 
-}
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base as TV


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Surjection

open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.Ring.Properties
open RingTheory

import Cubical.HITs.SetQuotients.Base as SQ
import Cubical.HITs.SetQuotients.Properties as SQ

open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.Quotient.Base


data TermsOf_[_] {ℓ ℓ' : Level} (R : CommRing ℓ) (I : Type ℓ') : Type (ℓ-max ℓ ℓ') where
    Tvar   : I     → TermsOf R [ I ]
    Tconst : fst R → TermsOf R [ I ]
    _+T_   : TermsOf R [ I ] → TermsOf R [ I ] → TermsOf R [ I ]
    -T_    : TermsOf R [ I ] → TermsOf R [ I ]
    _·T_   : TermsOf R [ I ] → TermsOf R [ I ] → TermsOf R [ I ] 
 
module _ {ℓ ℓ' : Level} {R : CommRing ℓ} {I : Type ℓ'} where
  open Construction R
  
  includeTerm : TermsOf R [ I ] → ⟨ R [ I ] ⟩ 
  includeTerm (Tvar i)   = TV.var i
  includeTerm (Tconst r) = R[_].const r
  includeTerm (x +T y)   = includeTerm x + includeTerm y
  includeTerm (-T x)     = - includeTerm x
  includeTerm (x ·T y)   = includeTerm x · includeTerm y 

  private 
    opaque
      unfolding TV.var
      fiberVar : (x : I) → fiber includeTerm (R[_].var x)
      fiberVar x = Tvar x , refl
    
      fiberVar' : (x : I) → ∥ fiber includeTerm (R[_].var x) ∥₁
      fiberVar' x = ∣ fiberVar x ∣₁
  
    fiberConst : (r : ⟨ R ⟩ ) → fiber includeTerm (R[_].const r)
    fiberConst r = Tconst r , refl
  
    fiberConst' : (r : ⟨ R ⟩ ) → ∥ fiber includeTerm (R[_].const r) ∥₁
    fiberConst' r = ∣ fiberConst r ∣₁
  
    fiber+ : (x y : ⟨ R [ I ] ⟩) → fiber includeTerm x → fiber includeTerm y → fiber includeTerm (x + y) 
    fiber+ x y (fx , πfx=x) (fy , πfy=y) = (fx +T fy) , cong₂ _+_ πfx=x πfy=y
    
    fiber+' : {x y : ⟨ R [ I ] ⟩} → ∥ fiber includeTerm x ∥₁ → ∥ fiber includeTerm y ∥₁ → ∥ fiber includeTerm (x + y) ∥₁
    fiber+' {x} {y} = map2 (fiber+ x y) 
  
    fiber· : (x y : ⟨ R [ I ] ⟩) → fiber includeTerm x → fiber includeTerm y → fiber includeTerm (x · y) 
    fiber· x y (fx , πfx=x) (fy , πfy=y) = (fx ·T fy) , cong₂ _·_ πfx=x πfy=y
    
    fiber·' : {x y : ⟨ R [ I ] ⟩} → ∥ fiber includeTerm x ∥₁ → ∥ fiber includeTerm y ∥₁ → ∥ fiber includeTerm (x · y) ∥₁
    fiber·' {x} {y} = map2 (fiber· x y) 
  
    fiber- : (x : ⟨ R [ I ] ⟩) → fiber includeTerm x → fiber includeTerm (- x ) 
    fiber- x (fx , πfx=x) = (-T fx) , cong -_ πfx=x 
    
    fiber-' : {x : ⟨ R [ I ] ⟩} → ∥ fiber includeTerm x ∥₁ → ∥ fiber includeTerm (- x ) ∥₁
    fiber-' {x} = map (fiber- x)
    
    fiberPathType : 
      {lhs rhs : ⟨ R [ I ] ⟩ } → 
      {fibL : ∥ fiber includeTerm lhs ∥₁ } → 
      {fibR : ∥ fiber includeTerm rhs ∥₁ } → 
      (p : lhs ≡ rhs ) → 
      Type _ -- PathP (λ { i → ∥ fiber includeTerm (p i) ∥₁ }) fx fy 
    fiberPathType {lhs} {rhs} {fibL} {fibR} p = 
      PathP (λ { i → ∥ fiber includeTerm (p i) ∥₁ }) fibL fibR
    
    fiberPath : 
      {lhs rhs : ⟨ R [ I ] ⟩ } → 
      (p : lhs ≡ rhs) → 
      (fibL : ∥ fiber includeTerm lhs ∥₁ ) → 
      (fibR : ∥ fiber includeTerm rhs ∥₁ ) → 
      PathP (λ { i → ∥ fiber includeTerm (p i) ∥₁ }) fibL fibR
    fiberPath {x} {y} p fx fy = ∥∥-isPropDep (fiber includeTerm) fx fy p 
    
    fiber·-lid : 
      {x : ⟨ R [ I ] ⟩ } → 
      (fx : ∥ fiber includeTerm x ∥₁ ) → 
      fiberPathType (·-lid x)
    fiber·-lid {x} fx = fiberPath (·-lid x) (fiber·' (fiberConst' _) fx) fx 
    
    fiber+-rid : 
      {x : ⟨ R [ I ] ⟩ } → 
      (fx : ∥ fiber includeTerm x ∥₁ ) → 
      fiberPathType (+-rid x)
    fiber+-rid {x} fx = fiberPath (+-rid x)
      (fiber+' fx (fiberConst' _) ) fx 
    
    fiber+-rinv : 
      {x : ⟨ R [ I ] ⟩ } → 
      (fx : ∥ fiber includeTerm x ∥₁ ) → 
      fiberPathType (+-rinv x)
    fiber+-rinv {x} fx = fiberPath (+-rinv x)
      (fiber+' fx (fiber-' fx)) (fiberConst' _) 
    
    fiber+-comm : 
      {x y : ⟨ R [ I ] ⟩ } → 
      (fx : ∥ fiber includeTerm x ∥₁) → 
      (fy : ∥ fiber includeTerm y ∥₁) → 
      fiberPathType (+-comm x y)
    fiber+-comm {x} {y} fx fy = fiberPath (+-comm x y)
      (fiber+' fx fy) (fiber+' fy fx) 
    
    fiber·-comm : 
      {x y : ⟨ R [ I ] ⟩ } → 
      (fx : ∥ fiber includeTerm x ∥₁) → 
      (fy : ∥ fiber includeTerm y ∥₁) → 
      fiberPathType (·-comm x y ) 
    fiber·-comm {x} {y} fx fy = fiberPath (·-comm x y) 
      (fiber·' fx fy) (fiber·' fy fx)
    
    fiber+HomConst : 
      {r s : ⟨ R ⟩ } → 
      fiberPathType (+HomConst r s)
    fiber+HomConst {r} {s} = fiberPath (+HomConst r s)
       (fiberConst' ((snd R CommRingStr.+ r) s)) (fiber+' (fiberConst' r) (fiberConst' s))
    
    fiber·HomConst : 
      {r s : ⟨ R ⟩ } → 
      fiberPathType (·HomConst r s)
    fiber·HomConst {r} {s} = fiberPath (·HomConst r s)
       (fiberConst' ((snd R CommRingStr.· r) s)) (fiber·' (fiberConst' r) (fiberConst' s))
    
    fiber+-assoc : 
      {x y z : ⟨ R [ I ] ⟩ } → 
      (fx : ∥ fiber includeTerm x ∥₁) → 
      (fy : ∥ fiber includeTerm y ∥₁) → 
      (fz : ∥ fiber includeTerm z ∥₁) → 
      fiberPathType (+-assoc x y z)
    fiber+-assoc {x} {y} {z} fx fy fz = fiberPath (+-assoc x y z) 
      (fiber+' fx (fiber+' fy fz)) (fiber+'(fiber+' fx fy) fz)
    
    fiber·-assoc : 
      {x y z : ⟨ R [ I ] ⟩ } → 
      (fx : ∥ fiber includeTerm x ∥₁) → 
      (fy : ∥ fiber includeTerm y ∥₁) → 
      (fz : ∥ fiber includeTerm z ∥₁) → 
      fiberPathType (·-assoc x y z)
    fiber·-assoc {x} {y} {z} fx fy fz = fiberPath (·-assoc x y z)
      (fiber·' fx (fiber·' fy fz)) (fiber·'(fiber·' fx fy) fz)
    
    fiberldist : 
      {x y z : ⟨ R [ I ] ⟩ } → 
      (fx : ∥ fiber includeTerm x ∥₁) → 
      (fy : ∥ fiber includeTerm y ∥₁) → 
      (fz : ∥ fiber includeTerm z ∥₁) → 
      fiberPathType (ldist x y z)
    fiberldist {x} {y} {z} fx fy fz = fiberPath (ldist x y z)
      (fiber·' (fiber+' fx fy) fz) (fiber+' (fiber·' fx fz) (fiber·' fy fz)) 
    
    fiber0-trunc : 
        (x y : ⟨ R [ I ] ⟩) → 
        (fx : ∥ fiber includeTerm x ∥₁) → 
        (fy : ∥ fiber includeTerm y ∥₁) → 
        (p q : x ≡ y) → 
        (fp : PathP (λ j → ∥ fiber includeTerm (p j) ∥₁) fx fy) → 
        (fq : PathP (λ j → ∥ fiber includeTerm (q j) ∥₁) fx fy) → 
        PathP (λ i → PathP (λ j → ∥ fiber includeTerm (0-trunc x y p q i j) ∥₁)  fx fy ) fp fq 
    fiber0-trunc x y fx fy p q fp fq = isPropDep→isSetDep 
      (∥∥-isPropDep (fiber includeTerm)) fx fy fp fq ( 0-trunc x y p q )
    
  hasTerm : isSurjection includeTerm
  hasTerm (R[_].var   v)        = fiberVar'   v
  hasTerm (R[_].const r)        = fiberConst' r
  hasTerm (x + y)               = fiber+'      (hasTerm x) (hasTerm y)
  hasTerm (x · y)               = fiber·'      (hasTerm x) (hasTerm y)
  hasTerm (- x)                 = fiber-'      (hasTerm x)
  hasTerm (+-rid     x     i)   = fiber+-rid   (hasTerm x)                         i
  hasTerm (+-rinv    x     i)   = fiber+-rinv  (hasTerm x)                         i
  hasTerm (·-lid     x     i)   = fiber·-lid   (hasTerm x)                         i
  hasTerm (+-comm    x y   i)   = fiber+-comm  (hasTerm x) (hasTerm y)             i
  hasTerm (·-comm    x y   i)   = fiber·-comm  (hasTerm x) (hasTerm y)             i 
  hasTerm (+-assoc   x y z i)   = fiber+-assoc (hasTerm x) (hasTerm y) (hasTerm z) i 
  hasTerm (·-assoc   x y z i)   = fiber·-assoc (hasTerm x) (hasTerm y) (hasTerm z) i
  hasTerm (ldist     x y z i)   = fiberldist   (hasTerm x) (hasTerm y) (hasTerm z) i
  hasTerm (+HomConst r s   i)   = fiber+HomConst                                   i
  hasTerm (·HomConst r s   i)   = fiber·HomConst                                   i
  hasTerm (0-trunc x y p q i j) = fiber0-trunc x y (hasTerm x) (hasTerm y) p q 
                                       (λ i → hasTerm (p i)) (λ i → hasTerm (q i)) i j
