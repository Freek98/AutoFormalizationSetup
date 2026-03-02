{-# OPTIONS --cubical --guardedness #-}

module TerminalBA where 

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_)
open import Cubical.Data.Empty renaming (rec to ex-falso)

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base

open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Unit
open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Group

-- This module should go into BooleanRing.Instances.
module _ where
  open BooleanRingStr
  open IsBooleanRing
  open IsCommRing
  open IsRing 
  open IsAbGroup
  open IsMonoid
  open IsSemigroup
  open IsGroup
  
  UnitBRStr : BooleanRingStr Unit
  𝟘 UnitBRStr = tt
  𝟙 UnitBRStr = tt
  BooleanRingStr._+_ UnitBRStr _ _ = tt
  BooleanRingStr._·_ UnitBRStr _ _ = tt
  (- UnitBRStr) _ = tt
  is-set (isSemigroup (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (isBooleanRing UnitBRStr))))))) 
          = isSetUnit
  ·Assoc (isSemigroup (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (isBooleanRing UnitBRStr))))))) 
    _ _ _ = refl
  ·IdR (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (isBooleanRing UnitBRStr)))))) 
    _     = refl
  ·IdL (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (isBooleanRing UnitBRStr)))))) 
    _     = refl
  ·InvR (isGroup (+IsAbGroup (isRing (isCommRing (isBooleanRing UnitBRStr))))) 
    _     = refl
  ·InvL (isGroup (+IsAbGroup (isRing (isCommRing (isBooleanRing UnitBRStr))))) 
    _     = refl
  +Comm (+IsAbGroup (isRing (isCommRing (isBooleanRing UnitBRStr)))) 
    _ _   = refl
  is-set (isSemigroup (·IsMonoid (isRing (isCommRing (isBooleanRing UnitBRStr))))) 
          = isSetUnit
  ·Assoc (isSemigroup (·IsMonoid (isRing (isCommRing (isBooleanRing UnitBRStr))))) 
    _ _ _ = refl
  ·IdR (·IsMonoid (isRing (isCommRing (isBooleanRing UnitBRStr)))) 
    _     = refl
  ·IdL (·IsMonoid (isRing (isCommRing (isBooleanRing UnitBRStr)))) 
    _     = refl
  ·DistR+ (isRing (isCommRing (isBooleanRing UnitBRStr))) 
    _ _ _ = refl
  ·DistL+ (isRing (isCommRing (isBooleanRing UnitBRStr))) 
    _ _ _ = refl
  ·Comm (isCommRing (isBooleanRing UnitBRStr)) 
    _ _   = refl
  ·Idem (isBooleanRing UnitBRStr) 
    _     = refl
  
  UnitBR : BooleanRing ℓ-zero
  UnitBR = Unit , UnitBRStr
  
-- This module should go into BooleanRing.Terminal  
module _ { ℓ : Level} (B : BooleanRing ℓ) where
  private
    B' = BooleanRing→CommRing B
  open BooleanRingStr (snd B)
  open IsCommRingHom
  terminalBR : BoolHom B UnitBR
  fst terminalBR = terminal ⟨ B ⟩
  pres0 (snd terminalBR)     = refl
  pres1 (snd terminalBR)     = refl
  pres+ (snd terminalBR) _ _ = refl
  pres· (snd terminalBR) _ _ = refl
  pres- (snd terminalBR) _   = refl 

  isTrivial : Type ℓ 
  isTrivial = 𝟘 ≡ 𝟙  

  module _ (0=1 : isTrivial) where
    triv→Prop : {x y : ⟨ B ⟩} → x ≡ y
    triv→Prop {x} {y} = 
      x     ≡⟨ solve! B' ⟩ 
      𝟙 · x ≡⟨ (cong (λ a → a · x) $ sym 0=1) ⟩  
      𝟘 · x ≡⟨ solve! B' ⟩ 
      𝟘     ≡⟨ solve! B' ⟩ 
      𝟘 · y ≡⟨ cong (λ a → a · y) 0=1 ⟩ 
      𝟙 · y ≡⟨ solve! B' ⟩ 
      y     ∎ 
  
    triv→B≃UnitBR : isEquiv $ terminal ⟨ B ⟩
    fst (fst (equiv-proof triv→B≃UnitBR _ ))  = 𝟘 
    snd (fst (equiv-proof triv→B≃UnitBR _ ))  = refl
    snd (     equiv-proof triv→B≃UnitBR _  ) _ = Σ≡Prop (λ b → isSetUnit _ _) triv→Prop
  
  
